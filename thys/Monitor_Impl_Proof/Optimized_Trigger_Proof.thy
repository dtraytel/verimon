(*<*)
theory Optimized_Trigger_Proof
  imports "Monitor_Impl.Optimized_Trigger" Optimized_Common_Proof
begin
(*>*)


lemma valid_nmtaux_distinct:
  assumes "valid_nmtaux args cur aux auxlist"
  shows "distinct (args_L args)" "distinct (args_R args)"
  using assms by (cases aux, unfold valid_nmtaux_def prod.case, blast)+

lemma valid_init_nmtaux: "(
    if (mem I 0)
      then
        set L \<subseteq> set R
      else 
        L = R
    ) \<Longrightarrow>
    distinct L \<Longrightarrow> distinct R \<Longrightarrow>
    \<not>mem I 0 \<longrightarrow> pos \<Longrightarrow>
    let args = init_args I n L R pos agg in
    valid_nmtaux args 0 (init_mmtaux args) []"
  unfolding init_mmtaux_def
  by (simp add: init_args_def empty_queue_rep valid_nmtaux_def
      safe_max_def table_def newest_tuple_in_mapping_def
      ts_tuple_rel_binary_def ts_tuple_rel_f_def
      auxlist_data_prev_def auxlist_data_in_def Queue.is_empty_alt tuple_since_tp_def tuple_since_lhs_def)

lemma sorted_filter_dropWhile_memL:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). memL (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) (x#xs) = filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) xs"
      by auto
    moreover have "dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) xs)"
      by auto
    have dropWhile_IH: "dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = x#xs"
      using not_mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) (x#xs) = x#xs"
        using filter_IH
        by auto
      then show ?thesis using dropWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) x)" by auto
      then show ?thesis using not_mem by auto
    qed
  qed
qed

lemma sorted_filter_dropWhile_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) (x#xs) = filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs"
      by auto
    moreover have "dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case mem: False
    then have filter_IH: "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs)"
      by auto
    have dropWhile_IH: "dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = x#xs"
      using mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) (x#xs) = x#xs"
        using filter_IH
        by auto
      then show ?thesis using dropWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x)" using memR_antimono by auto
      then show ?thesis using mem by auto
    qed
  qed
qed

lemma sorted_filter_takeWhile_memL:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). memL (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _).memL (args_ivl args) (mt - t)) xs)"
      by auto
    moreover have "takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = x#(takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = (filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs)"
      by auto
    have takeWhile_IH: "takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = []"
      using not_mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = []"
        using filter_IH
        by (simp add: case_prod_beta')
      then show ?thesis using takeWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) x)" by auto
      then show ?thesis using not_mem by auto
    qed
  qed
qed

lemma sorted_filter_takeWhile_not_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _).\<not>memR (args_ivl args) (mt - t)) xs)"
      by auto
    moreover have "takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = x#(takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = (filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs)"
      by auto
    have takeWhile_IH: "takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = []"
      using not_mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = []"
        using filter_IH
        by (simp add: case_prod_beta')
      then show ?thesis using takeWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x)"
        using memR_antimono by auto
      then show ?thesis using not_mem by auto
    qed
  qed
qed

lemma data_in_mem:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> set (linearize data_in)"
  shows "mem (args_ivl args) (mt - (fst db))"
proof (cases db)
  case (Pair t r)
  from assms(1) have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
    unfolding valid_nmtaux_def prod.case by blast
  then have "(t, r) \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
    using Pair assms(2)
    by auto
  then obtain l where "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
    by auto
  then show ?thesis
    unfolding auxlist_data_in_def
    using set_filter[of "\<lambda>(t, _, _). mem (args_ivl args) (mt - t)" auxlist] Pair
    by auto
qed

lemma data_prev_mem:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> set (linearize data_prev)"
  shows "\<not>memL (args_ivl args) (mt - (time db))"
proof -
  from assms(1) have "auxlist_data_prev args mt auxlist = linearize data_prev"
    unfolding valid_nmtaux_def prod.case by blast
  then have "db \<in> set (auxlist_data_prev args mt auxlist)" using assms(2) by auto
  then show ?thesis
    unfolding auxlist_data_prev_def time_def
    using set_filter[of "\<lambda>(t, _, _). \<not>memL (args_ivl args) (mt - t)" auxlist]
    by auto
qed


lemma data_sorted:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "sorted (map fst (linearize data_prev))" "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` (set (linearize data_in)). \<forall>t' \<in> fst ` (set (linearize data_prev)). t < t'"
proof -
  from assms have sorted: "sorted (map fst auxlist)"
    unfolding valid_nmtaux_def prod.case by blast
  from assms have data_props: 
    "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
    unfolding valid_nmtaux_def prod.case by blast+
  
  show "sorted (map fst (linearize data_prev))"
    using data_props(1) sorted sorted_filter
    unfolding auxlist_data_prev_def
    by metis

  have "\<forall>tuple. fst ((\<lambda> (t, l, r). (t, r)) tuple) = fst tuple"
    by auto
  then have "map fst (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)) = map fst (auxlist_data_in args mt auxlist)"
    by auto

  moreover from sorted have "sorted (map fst (auxlist_data_in args mt auxlist))"
    unfolding auxlist_data_in_def
    using sorted_filter
    by auto

  ultimately have "sorted (map fst (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)))"
    by (simp only: )

  then show "sorted (map fst (linearize data_in))"
    using data_props(2)
    by simp

  {
    fix t t'
    assume "t \<in> fst ` (set (linearize data_in))" "t' \<in> fst ` (set (linearize data_prev))"
    then have memL: "\<not>memL (args_ivl args) (mt - t')" "memL (args_ivl args) (mt - t)"
      using data_in_mem[OF assms(1)] data_prev_mem[OF assms(1)]
      unfolding time_def
      by auto
    {
      assume "t \<ge> t'"
      then have "False" using memL memL_mono by auto
    }
    then have "t < t'" using not_le_imp_less by blast
  }
  then show "\<forall>t \<in> fst ` (set (linearize data_in)). \<forall>t' \<in> fst ` (set (linearize data_prev)). t < t'" by auto
qed

lemma tuple_in_once_mem0:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "mem (args_ivl args) 0"
  shows "tuple_in_once = Mapping.empty"
proof -
  from assms(2) have memL_all: "\<forall>t. memL (args_ivl args) t" by auto
  from assms(1) have "auxlist_data_prev args mt auxlist = linearize data_prev"
    unfolding valid_nmtaux_def prod.case by blast
  then have "linearize data_prev = []"
    using memL_all
    unfolding auxlist_data_prev_def
    by auto
  moreover from assms(1) have "(\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l as)"
    unfolding valid_nmtaux_def prod.case by blast
  ultimately have "Mapping.keys tuple_in_once = {}"
    using Mapping.in_keysD
    by fastforce
  then show ?thesis
    by (simp add: keys_dom_lookup mapping_eqI)
qed

lemma auxlist_mem_or:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> (set auxlist)"
  shows "(((\<lambda> (t, l, r). (t, r)) db) \<in> set (linearize data_in) \<and> db \<notin> set (linearize data_prev)) \<and> memL (args_ivl args) (mt - time db) \<or> (((\<lambda> (t, l, r). (t, r)) db) \<notin> set (linearize data_in) \<and> db \<in> set (linearize data_prev)) \<and> \<not>memL (args_ivl args) (mt - time db)"
proof (cases "memL (args_ivl args) (mt - (time db))")
  define db' where "db' = ((\<lambda> (t, l, r). (t, r)) db)"
  case True
  from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    unfolding valid_nmtaux_def prod.case by blast+
  from assms have mem: "memR (args_ivl args) (mt - time db)" unfolding valid_nmtaux_def prod.case by blast

  {
    assume "db \<in> set (linearize data_prev)"
    then have "db \<in> set (auxlist_data_prev args mt auxlist)"
      using data_props(1)
      by auto
    then have "\<not>memL (args_ivl args) (mt - (time db))"
      unfolding auxlist_data_prev_def time_def
      by auto
    then have "False"
      using True
      by auto
  }
  then have not_prev: "db \<notin> set (linearize data_prev)" by auto

  have db_mem: "db \<in> set (auxlist_data_in args mt auxlist)"
    using True assms(2) mem
    unfolding auxlist_data_in_def time_def
    by auto
  then have "(\<lambda> (t, l, r). (t, r)) db \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
    by auto
  then have "db' \<in> set (linearize data_in)"
    using data_props(2) db'_def
    by auto
  moreover have "memL (args_ivl args) (mt - time db)"
    using db_mem
    unfolding auxlist_data_in_def time_def
    by auto
  ultimately show ?thesis using db'_def not_prev by blast
next
  define db' where "db' = ((\<lambda> (t, l, r). (t, r)) db)"
  case False
  from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    unfolding valid_nmtaux_def prod.case by blast+
  from assms have mem: "memR (args_ivl args) (mt - time db)" unfolding valid_nmtaux_def prod.case by blast
  have time_eq: "fst db = fst db'" using db'_def by (simp add: case_prod_beta)

  {
    assume "db' \<in> set (linearize data_in)"
    then have "db' \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
      using data_props(2)
      by auto
    then have "\<exists>l. (fst db', l, snd db') \<in> set (auxlist_data_in args mt auxlist)"
      by auto
    then have "mem (args_ivl args) (mt - (time db))"
      using time_eq
      unfolding auxlist_data_in_def time_def
      by auto
    then have "False"
      using False
      by auto
  }
  then have not_in: "db' \<notin> set (linearize data_in)" by auto
  
  have "db \<in> set (auxlist_data_prev args mt auxlist)"
    using False assms(2)
    unfolding auxlist_data_prev_def time_def
    by auto
  then have "db \<in> set (linearize data_prev)"
    using data_props(1) db'_def
    by auto
  then show ?thesis using not_in db'_def False by blast
qed

lemma auxlist_mem_data_in:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> set auxlist"
  assumes "mem (args_ivl args) (mt - (time db))"
  shows "(\<lambda> (t, l, r). (t, r)) db \<in> set (linearize data_in)"
  using auxlist_mem_or[OF assms(1) assms(2)] assms(3)
  by auto


lemma data_prev_ts_props:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> mt \<and> \<not> memL (args_ivl args) (cur - t)"
proof -
  from assms have data_props:
    "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    unfolding valid_nmtaux_def prod.case by blast
  from assms have "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db))"
    unfolding valid_nmtaux_def prod.case by blast
  moreover from assms have time: "cur = mt" unfolding valid_nmtaux_def prod.case by blast
  ultimately have memR: "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (cur - time db))"
    by auto

  {
    fix t
    assume "t \<in> fst ` set (linearize data_prev)"
    then obtain db where db_props: "t = fst db" "db \<in> set (linearize data_prev)"
      by auto
    then have "db \<in> set (auxlist_data_prev args mt auxlist)" using data_props by auto
    then have "\<not>memL (args_ivl args) (cur - t)" "db \<in> set auxlist"
      unfolding auxlist_data_prev_def db_props(1)
      using time
      by auto
    moreover have "t \<le> mt"
      using calculation(2) memR
      unfolding time_def db_props(1)
      by auto
    ultimately have "t \<le> mt" "\<not>memL (args_ivl args) (cur - t)" by auto
  }
  then show ?thesis by auto
qed

lemma data_in_ts_props:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "\<forall>t \<in> fst ` set (linearize data_in). t \<le> mt \<and> memL (args_ivl args) (cur - t)"
proof -
  from assms have data_props:
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
    "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
    unfolding valid_nmtaux_def prod.case by blast+
  from assms have "(\<forall>db \<in> set auxlist. time db \<le> mt \<and>  memR (args_ivl args) (mt - time db))"
    unfolding valid_nmtaux_def prod.case by blast
  moreover from assms have time: "cur = mt" unfolding valid_nmtaux_def prod.case by blast
  ultimately have memR: "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (cur - time db))"
    by auto

  {
    fix t
    assume "t \<in> fst ` set (linearize data_in)"
    then obtain db where db_props: "t = fst db" "db \<in> set (linearize data_in)"
      by auto
    then obtain db' where db'_props: "db = (\<lambda> (t, l, r). (t, r)) db'" "db' \<in> set (auxlist_data_in args mt auxlist)"
      using data_props(1)
      by (metis (no_types, lifting) image_iff image_set)
    then have same_time: "fst db' = t"
      unfolding db_props(1)
      by (simp add: case_prod_beta)

    then have "mem (args_ivl args) (cur - t)" "db' \<in> set auxlist"
      using db'_props(2) time
      unfolding auxlist_data_in_def
      by auto
    moreover have "t \<le> mt"
      using calculation(2) memR same_time
      unfolding time_def db_props(1)
      by auto
    ultimately have "t \<le> mt" "memL (args_ivl args) (cur - t)" by auto
  }
  then show ?thesis by auto
qed

lemma auxlist_index_time_mono:
  assumes "valid_nmtaux args cur (nt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "i \<le> j" "j \<in> {0..<(length auxlist)}"
  shows "fst (auxlist!i) \<le> fst (auxlist!j)"
proof -
  from assms have "sorted (map fst auxlist)" unfolding valid_nmtaux_def prod.case by blast
  then have sorted: "\<forall>i. \<forall>j \<in> {0..<(length auxlist)}.
    i \<le> j \<longrightarrow> fst (auxlist!i) \<le> fst (auxlist!j)"
    by (simp add: sorted_iff_nth_mono)
  then show "fst (auxlist!i) \<le> fst (auxlist!j)"
    using sorted assms(2-3)
    by auto
qed

lemma auxlist_time_index_strict_mono:
  assumes "valid_nmtaux args cur (nt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "i \<in> {0..<(length auxlist)}"
  assumes "fst (auxlist!i) < fst (auxlist!j)" (* t < t' *)
  shows "i < j"
proof -
    {
      assume assm: "j \<le> i"
      then have "False"
        using auxlist_index_time_mono[OF assms(1) assm assms(2)] assms(3)
        by auto
    }
    then show "i < j" using not_le_imp_less by blast
  qed

lemma data_in_auxlist_nonempty:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0) = (\<not> Queue.is_empty (data_in))"
proof (rule iffI)
  assume assm: "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
  {
    assume empty: "set (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) = {}"
    {
      assume "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
      then have "\<exists>x. x \<in> set (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist)"
        using nth_mem by blast
      then have "False" using empty by auto
    }
    then have "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) = 0"
      by auto
    then have "False" using assm by auto
  }
  then obtain db where db_props: "db \<in> set (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist)"
    by auto
  then have "db \<in> set auxlist" "mem (args_ivl args) (mt - fst db)" by auto
  then have "(\<lambda> (t, l, r). (t, r)) db \<in> set (linearize data_in)"
    using auxlist_mem_data_in[OF assms(1), of db]
    unfolding time_def
    by blast
  then have "set (linearize data_in) \<noteq> {}" by auto
  then show "\<not> Queue.is_empty (data_in)"
    using Queue.is_empty_alt
    by auto
next
    from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
      unfolding valid_nmtaux_def prod.case by blast+

    assume "\<not> Queue.is_empty (data_in)"
    then have "set (linearize data_in) \<noteq> {}" using Queue.is_empty_alt by auto
    then obtain db where db_props: "db \<in> set (linearize data_in)"
      by (meson equals0I)
    then have db_mem: "db \<in> set (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist))"
      using data_props(2)
      unfolding auxlist_data_in_def
      by auto
    then obtain l where "(fst db, l, snd db) \<in> set (filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist)"
      by auto
    then show auxlist_nonempty: "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0)"
      using length_pos_if_in_set[of "(fst db, l, snd db)" "filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist"]
      by auto
  qed

lemma valid_nmtaux_nonempty:
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0) = (\<not> Queue.is_empty data_in)"
proof -
  from assms(1) have data_in_equiv:
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
      unfolding valid_nmtaux_def prod.case by blast
    show ?thesis
    proof (rule iffI)
      assume "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
      then have "length (auxlist_data_in args mt auxlist) > 0"
        using auxlist_data_in_def[of args mt auxlist]
        by auto
      then have "{} \<noteq> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"        
        by auto
      then have "(linearize data_in) \<noteq> []"
        using data_in_equiv
        by auto
      then show "\<not> Queue.is_empty data_in"
        using Queue.is_empty_alt
        by auto
    next
      assume "\<not> Queue.is_empty data_in"
      then have "\<exists>e. e \<in> set (linearize data_in)"
        using Queue.is_empty_alt nth_mem
        by blast
      then have "{} \<noteq> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
        using data_in_equiv
        by auto
      then have "{} \<noteq> set (auxlist_data_in args mt auxlist)"
        by auto
      then have "length (auxlist_data_in args mt auxlist) > 0"
        by auto 
      then show "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
        unfolding auxlist_data_in_def 
        by auto
    qed
  qed

lemma valid_result_nmtaux_unfolded: 
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "result_nmtaux args (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) = trigger_results args cur auxlist"
proof -
  define aux where "aux = (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)"
  define I where "I = args_ivl args"
  from assms(1) have time: "mt = cur" unfolding valid_nmtaux_def prod.case by blast
  from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    unfolding valid_nmtaux_def prod.case by blast+
  from assms(1) have sorted: "sorted (map fst auxlist)"
    unfolding valid_nmtaux_def prod.case by blast
  {
    assume non_empty_assm: "\<not>Queue.is_empty data_in"
    note non_empty_alt = non_empty_assm data_in_auxlist_nonempty[OF assms(1)] time
  
    {
      fix tuple
      assume assm: "tuple \<in> snd (result_nmtaux args aux)"
      then have non_empty: "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
        using non_empty_assm valid_nmtaux_nonempty[OF assms(1)]
        by auto
  
      {
        assume "tuple \<in> hist_sat"
        then have hist:
          "\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r"
          "(\<not>Queue.is_empty data_in)"
          "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
          "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in))). wf_tuple (args_R args) as)"
          using assms(1)
          unfolding valid_nmtaux_def prod.case by blast+
        then obtain t l r where "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
          using Queue.is_empty_alt[of data_in]
          by (metis length_greater_0_conv length_map nth_mem proj_thd.cases)
        then have "tuple \<in> r" "(t, r) \<in> set (linearize data_in)"
          using hist(1) set_map[of "(\<lambda> (t, l, r). (t, r))" "(auxlist_data_in args mt auxlist)", unfolded hist(3)]
          by (auto simp add: rev_image_eqI)
        then have wf: "wf_tuple (args_R args) tuple"
          using hist(4)
          by auto
        {
          fix i
          assume i_props: "i \<in> {0..<(length auxlist)}" "mem (args_ivl args) (mt - fst (auxlist!i))"
          then have "auxlist!i \<in> set (auxlist_data_in args mt auxlist)"
            by (simp add: auxlist_data_in_def case_prod_unfold)
          then have "tuple \<in> (snd o snd) (auxlist!i)" using hist by auto
        }
        then have "(\<forall>i \<in> {0..<(length auxlist)}.
          let (t, l, r) = auxlist!i in
          mem (args_ivl args) (mt - t) \<longrightarrow> tuple \<in> r
        )" by (simp add: case_prod_beta')
        then have "tuple \<in> snd (trigger_results args mt auxlist)"
          using non_empty wf
          by auto
      }
      then have hist_sat_mem: "tuple \<in> hist_sat \<Longrightarrow> tuple \<in> snd (trigger_results args mt auxlist)"
        by auto

      have "tuple_in_once_keys = Mapping.keys tuple_in_once"
        using assms(1)
        unfolding valid_nmtaux_def prod.case by blast
      then have "tuple \<in> (Mapping.keys tuple_in_once) \<or> tuple \<in> hist_sat \<or> tuple \<in> since_sat"
        using assm non_empty_assm
        by (simp add: aux_def split: if_splits)
      moreover {
        assume assm: "tuple \<in> (Mapping.keys tuple_in_once)"
        then have "newest_tuple_in_mapping fst data_prev tuple_in_once (\<lambda>x. True)"
          using assms(1)
          unfolding valid_nmtaux_def prod.case by blast
        then have "Mapping.lookup tuple_in_once tuple =
          safe_max (
            fst ` {
             tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)).
             tuple = snd tas
            }
          )"
          unfolding newest_tuple_in_mapping_def
          by auto
        moreover have "\<exists>t. Mapping.lookup tuple_in_once tuple = Some t"
          using assm
          by (simp add: Mapping.in_keysD)
        then obtain t where t_props: "Mapping.lookup tuple_in_once tuple = Some t"
          by auto
        from assms(1) have "\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l as"
          unfolding valid_nmtaux_def prod.case by blast
        then have "\<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l tuple"
          using assm t_props
          by fastforce
        then obtain db l r where db_props': "db = (t, l, r)" "db \<in> set (linearize data_prev)" "join_cond (args_pos args) l tuple"
          unfolding ts_tuple_rel_f_def
          by auto
        have "\<not>mem (args_ivl args) 0"
          using db_props'(1,2) data_props(1) memL_mono[of "args_ivl args" 0]
          unfolding auxlist_data_prev_def
          by auto
        then have L_R: "args_L args = args_R args"
          using assms(1)
          by (simp add: valid_nmtaux_def)
        have "table (args_L args) (Mapping.keys tuple_in_once)"
          using assms(1)
          unfolding valid_nmtaux_def prod.case by blast
        then have tuple_idle: "restrict (args_L args) (args_R args) tuple = tuple"
          using restrict_idle[OF valid_nmtaux_distinct(1)[OF assms(1)] tableD[OF _ assm]] L_R
          by auto
        have db_props: "db = (t, l, r)" "db \<in> set (linearize data_prev)" "join_cond (args_pos args) l (restrict (args_L args) (args_R args) tuple)"
          using db_props' unfolding tuple_idle by auto
        then obtain j where j_props: "db = auxlist!j" "j \<in> {0..<(length auxlist)}"
          using data_props(1)
          unfolding auxlist_data_prev_def
          by (metis (no_types, lifting) atLeastLessThan_iff filter_is_subset in_set_conv_nth leI not_less_zero subsetD)
        
        {
          fix i
          define dbi where "dbi = auxlist!i"
          assume i_props: "i \<in> {0..<(length auxlist)}" "mem (args_ivl args) (mt - time dbi)"
          {
            assume "j \<le> i"
            then have "fst (auxlist ! j) \<le> fst (auxlist ! i)"
              using sorted i_props(1)
              by (simp add: sorted_iff_nth_mono)
            then have j_memL: "memL (args_ivl args) (mt - time (auxlist!j))"
              using i_props(2) memL_mono[of "args_ivl args" "mt - time dbi" "mt - time (auxlist!j)"]
              unfolding time_def dbi_def
              by auto
            then have "auxlist!j \<in> set (linearize data_prev)"
              using j_props db_props
              by auto
            then have "\<not>memL (args_ivl args) (mt - time (auxlist!j))"
              using data_prev_mem[OF assms(1)]
              by auto
            then have "False" using j_memL by blast
          }
          then have j_ge_i: "i < j" using not_le_imp_less by blast
          then have "j \<in> {i<..<(length auxlist)}" using j_props(2)
            by simp
          moreover have "join_cond (args_pos args) ((fst o snd) (auxlist!j)) (restrict (args_L args) (args_R args) tuple)"
            using db_props j_props(1)
            by auto
          ultimately have "(\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
            )"
          using relL_def
          by metis
        }
        then have "(\<forall>i \<in> {0..<(length auxlist)}.
          let (t, l, r) = auxlist!i in
          mem (args_ivl args) (mt - t) \<longrightarrow>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
            )
        )"
          by (fastforce simp add: case_prod_beta' time_def)
        moreover have "wf_tuple (args_R args) tuple"
        proof -
          have "auxlist_data_prev args mt auxlist = (linearize data_prev)"
            using assms(1)
            unfolding valid_nmtaux_def prod.case by blast
          then have "auxlist_data_prev args mt auxlist \<noteq> []"
            using db_props
            by auto
          then have "\<not>mem (args_ivl args) 0"
            using memL_mono[of "args_ivl args" 0]
            unfolding auxlist_data_prev_def
            by auto
          then have "(args_L args) = (args_R args)"
            using assms(1)
            by (simp add: valid_nmtaux_def)
          then have "table (args_R args) (Mapping.keys tuple_in_once)"
            using assms(1)
            by (simp add: valid_nmtaux_def)
          then show ?thesis
            using assm
            unfolding table_def
            by blast
        qed                
        ultimately have "tuple \<in> snd (trigger_results args mt auxlist)"
          using non_empty
          unfolding relL_def
          by fastforce
      }
      moreover {
        assume "tuple \<in> since_sat"
        moreover have "(\<forall>tuple. tuple \<in> since_sat \<longrightarrow>
          ((tuple \<in> hist_sat) \<or> tuple_since_lhs tuple (linearize data_in) args (auxlist_data_in args mt auxlist))
        )"
          using assms(1)
          unfolding valid_nmtaux_def prod.case by blast
        moreover have "length (linearize data_in) = length (auxlist_data_in args mt auxlist)"
        proof -
          have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
            using assms(1)
            unfolding valid_nmtaux_def prod.case by blast
          then show ?thesis
            by (metis length_map)
        qed
        ultimately have "(tuple \<in> hist_sat) \<or> (\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
          let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (
              join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)
            )
          ))"
          unfolding tuple_since_lhs_def
          by fastforce
        moreover {
          assume "tuple \<in> hist_sat"
          then have "tuple \<in> snd (trigger_results args mt auxlist)"
            using hist_sat_mem by auto
        }
        moreover {
          assume "\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
          let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (
              join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)
            )
          )"
  
          then obtain n where n_def:
            "n \<in> {0..<length (auxlist_data_in args mt auxlist)}"
            "let suffix = drop n (auxlist_data_in args mt auxlist) in (
                (\<forall>(t, l, r) \<in> set suffix.
                  tuple \<in> r
                ) \<and>
                (
                  join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)
                )
            )"
            by blast
          define suffix where "suffix = drop n (auxlist_data_in args mt auxlist)"
          then have suffix_rhs: "\<forall>(t, l, r) \<in> set suffix. tuple \<in> r"
            using n_def(2)
            by meson
          
  
          have suffix_length: "length suffix > 0" "length suffix = length (auxlist_data_in args mt auxlist) - n"
            using suffix_def n_def(1)
            by auto
          then obtain t l r where tlr:
            "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
            "tuple \<in> r"
            using suffix_rhs
            unfolding suffix_def
            by (metis case_prodE hd_in_set in_set_dropD length_greater_0_conv)
          moreover have in_props:
            "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in))). wf_tuple (args_R args) as)"
            "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
            using assms(1)
            unfolding valid_nmtaux_def prod.case by blast+
          ultimately have "(t, r) \<in> set (linearize data_in)"
            by (metis (no_types, lifting) case_prod_conv list.set_map pair_imageI)
          then have wf: "wf_tuple (args_R args) tuple"
            using tlr in_props(1)
            by auto
  
          have idx_shift: "\<forall>i\<in>{0..<length suffix}. suffix!i = (auxlist_data_in args mt auxlist)!(i+n)"
            using suffix_def n_def(1)
            by (simp add: add.commute)
          have suffix_lhs: "join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)"
            using suffix_def n_def(2)
            by meson
          
          moreover have data_in_equiv: "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
            using assms(1)
            unfolding valid_nmtaux_def prod.case by blast
          moreover have "(auxlist_data_in args mt auxlist)!n = auxlist!n"
            using n_def(1)
            by (simp add: calculation(2))
          ultimately have since: "join_cond (args_pos args) (relL (auxlist!n)) (restrict (args_L args) (args_R args) tuple)"
            using idx_shift suffix_length
            unfolding suffix_def
            by (auto simp add: hd_drop_conv_nth)
          
          have n_le_auxlist: "n < (length auxlist)"
            using n_def(1)
            unfolding auxlist_data_in_def
            by (meson atLeastLessThan_iff diff_le_self length_filter_le less_le_trans)
          {
            fix i
            assume i_props: "i \<in> {0..<n}"
            then have "n \<in> {i<..<(length auxlist)}"
              using n_le_auxlist
              by auto
            moreover have
              "join_cond (args_pos args) (relL (auxlist!n)) (restrict (args_L args) (args_R args) tuple)"
              using since
              by auto
            ultimately have "(\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
              )"
              using relL_def by blast
          }
          then have "(\<forall>i \<in> {0..<n}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> 
              (\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
              )
          )"
            by (simp add: case_prod_beta')
          then have trigger_res_1: "(\<forall>i \<in> {0..<n}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> 
            (
              tuple \<in> r \<or>
              (\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
              )
            )
          )" by fastforce
          {
            fix i
            assume i_props: "i \<in> {n..<(length auxlist)}" "mem (args_ivl args) (mt - time (auxlist!i))"
            {
              assume "i \<ge> n + length suffix"
              then have i_ge: "i \<ge> length (auxlist_data_in args mt auxlist)"
                using suffix_length n_def(1)
                by auto
              then have idx_shift: "auxlist!i = (drop (length (auxlist_data_in args mt auxlist)) auxlist)!(i - length (auxlist_data_in args mt auxlist))"
                by (simp add: data_in_equiv)
              have
                "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
                "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
                using assms(1)
                unfolding valid_nmtaux_def prod.case by blast+
              then have data_prev_equiv: "auxlist_data_prev args mt auxlist = drop (length (auxlist_data_in args mt auxlist)) auxlist"
                by (metis length_map)
              then have "auxlist!i = (auxlist_data_prev args mt auxlist)!(i - length (auxlist_data_in args mt auxlist))"
                using idx_shift
                by auto
              then have "auxlist!i \<in> set (auxlist_data_prev args mt auxlist)"
                using i_ge i_props(1) data_prev_equiv
                by (metis (no_types, lifting) add.commute atLeastLessThan_iff in_set_conv_nth le_add_diff_inverse length_drop less_diff_conv)
              moreover have "auxlist_data_prev args mt auxlist = (linearize data_prev)"
                using assms(1)
                unfolding valid_nmtaux_def prod.case by blast
              ultimately have "auxlist!i \<in> set (linearize data_prev)" by auto
              then have "\<not> memL (args_ivl args) (mt - time (auxlist!i))"
                using data_prev_mem[OF assms(1), of "auxlist!i"]
                by auto
              then have "False" using i_props(2) by auto
            }
            then have "i < n + length suffix" using not_le_imp_less by blast
            then have "i < length (auxlist_data_in args mt auxlist)"
              using suffix_length
              by auto
            then have i_props': "i \<in> {n..<length (auxlist_data_in args mt auxlist)}"
              using i_props
              by auto
            then have "suffix!(i-n) = (auxlist_data_in args mt auxlist)!i"
              unfolding suffix_def
              by simp
            moreover have "(auxlist_data_in args mt auxlist)!i = auxlist!i"
              using data_in_equiv i_props'
              by simp
            ultimately have "suffix!(i-n) = auxlist!i" by auto
            moreover have "i - n < length suffix"
              using i_props' suffix_length(2)
              by auto
            ultimately have "auxlist!i \<in> set suffix"
              by (metis nth_mem)
            (* "\<forall>i\<in>{0..<length suffix}. suffix!i = (auxlist_data_in args mt auxlist)!(i+n)" *)
            then have "tuple \<in> (snd o snd) (auxlist!i)"
              using suffix_rhs
              by auto
          }
          then have "(\<forall>i \<in> {n..<(length auxlist)}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> tuple \<in> r
          )"
            unfolding time_def
            by (simp add: case_prod_beta')
          then have "(\<forall>i \<in> {n..<(length auxlist)}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> 
            (
              tuple \<in> r \<or>
              (\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
              )
            )
          )"
            by auto
          then have "(\<forall>i \<in> {0..<(length auxlist)}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> 
            (
              tuple \<in> r \<or>
              (\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
              )
            )
          )"
            using trigger_res_1
            by (meson atLeastLessThan_iff not_le_imp_less)
          then have "tuple \<in> snd (trigger_results args mt auxlist)"
            using non_empty wf
            unfolding relL_def
            by fastforce
        }
        ultimately have "tuple \<in> snd (trigger_results args mt auxlist)"
          by blast
      }
      ultimately have "tuple \<in> snd (trigger_results args mt auxlist)"
        using hist_sat_mem
        by blast
      then have "tuple \<in> snd (trigger_results args cur auxlist)"
        using time
        by auto
    }
    then have subset: "snd (result_nmtaux args aux) \<subseteq> snd (trigger_results args cur auxlist)"
      by blast
    {
      fix tuple
      assume el: "tuple \<in> snd (trigger_results args cur auxlist)"
      then have wf: "wf_tuple (args_R args) tuple"
        using non_empty_alt
        by auto
      have "(\<forall>i \<in> {0..<(length auxlist)}.
          let (t, l, r) = auxlist!i in
          mem (args_ivl args) (cur - t) \<longrightarrow> 
          (
            tuple \<in> r \<or>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
            )
          )
        )"
        using el non_empty_alt
        unfolding relL_def
        by fastforce
      then have tuple_props: "(\<forall>i \<in> {0..<(length auxlist)}.
          mem (args_ivl args) (cur - time (auxlist!i)) \<longrightarrow> 
          (
            tuple \<in> relR (auxlist!i) \<or>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
            )
          )
        )"
        using el
        unfolding relR_def time_def
        by (fastforce simp add: Let_def)
      {
        assume hist: "\<forall>i \<in> {0..<(length auxlist)}.
          mem (args_ivl args) (cur - time (auxlist!i)) \<longrightarrow> tuple \<in> relR (auxlist!i)"
        {
          fix db
          assume "db \<in> set (auxlist_data_in args mt auxlist)"
          then have db_props: "mem (args_ivl args) (cur - time db)" "db \<in> set auxlist"
            using time
            unfolding auxlist_data_in_def time_def
            by auto
          from db_props(2) obtain j where j_props:
              "j \<in> {0..<(length auxlist)}"
              "db = auxlist!j"
            by (metis atLeastLessThan_iff in_set_conv_nth leI not_less0)
          then have "tuple \<in> relR db"
            using hist db_props j_props
            by auto
        }
        then have "\<forall>db \<in> set (auxlist_data_in args mt auxlist). tuple \<in> relR db"
          by auto
        then have "\<forall>(t, r) \<in> set (map (\<lambda>(t, l, r). (t, r)) (auxlist_data_in args mt auxlist)). tuple \<in> r"
          unfolding relR_def
          by auto
        moreover have "(\<forall>tuple. tuple \<in> hist_sat \<longleftrightarrow>
          (\<not>Queue.is_empty data_in) \<and> (
            \<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r
        ))" using assms(1) unfolding valid_nmtaux_def prod.case by blast
        ultimately have "tuple \<in> hist_sat"
          using non_empty_alt
          by auto
        then have "tuple \<in> snd (result_nmtaux args aux)"
          using non_empty_alt
          unfolding aux_def
          by auto
      }
      moreover {
        assume "\<exists>i \<in> {0..<(length auxlist)}.
          mem (args_ivl args) (cur - time (auxlist!i)) \<and> tuple \<notin> relR (auxlist!i)"      
        then obtain i where i_props:
          "i \<in> {0..<(length auxlist)}"
          "mem (args_ivl args) (cur - time (auxlist!i))"
          "tuple \<notin> relR (auxlist!i)"
          by auto
  
        define A where "A = {j \<in> {i<..<(length auxlist)}. join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)}"
        define j where "j = Max A"
  
        have "\<exists>j \<in> {i<..<(length auxlist)}.
          join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
        "
          using i_props el tuple_props
          unfolding time_def relR_def
          by fastforce
        then have A_props: "A \<noteq> {}" "finite A" unfolding A_def by auto
        then have "j \<in> A" unfolding j_def by auto
        then have j_props:
          "j \<in> {i<..<(length auxlist)}"
          "join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)"
          using A_def
          by auto
  
        {
          define suffix where "suffix = drop j (auxlist_data_in args mt auxlist)"
          assume j_le: "j < length (linearize data_in)"
          (* length (auxlist_data_in args mt auxlist)-1 *)
          moreover have data_in_props: "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
            using assms(1)
            unfolding valid_nmtaux_def prod.case by blast
          ultimately have "hd suffix = auxlist!j"
            using data_props(2)
            unfolding suffix_def
            by (metis (no_types, lifting) hd_drop_conv_nth length_map nth_take)
          
  
          then have suffix_first: "join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)"
            using j_props
            by auto
  
          have "length (auxlist_data_in args mt auxlist) = length (linearize data_in)"
            using data_props(2)
            by (metis length_map)
          then have j_le: "j < length (auxlist_data_in args mt auxlist)"
            using j_le
            by auto
  
          {
            fix db
            assume suffix_mem: "db \<in> set suffix"
            then obtain k where k_props:
              "k \<in> {0..<length suffix}"
              "suffix!k = db"
              by (meson atLeastLessThan_iff less_eq_nat.simps(1) nth_the_index the_index_bounded)
            then have kj_props:
              "(k+j) \<in> {0..<length (auxlist_data_in args mt auxlist)}"
              "(auxlist_data_in args mt auxlist)!(k+j) = db"
              using suffix_def
              by (auto simp add: add.commute)
            then have "(k+j) \<in> {0..<length auxlist}"
              unfolding auxlist_data_in_def
              by (simp add: less_le_trans)
  
            then have cond: "
              mem (args_ivl args) (cur - time (auxlist!(k+j))) \<longrightarrow> 
              (
                tuple \<in> relR (auxlist!(k+j)) \<or>
                (\<exists>j \<in> {(k+j)<..<(length auxlist)}.
                  join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
                )
              )" using tuple_props by auto
  
  
            have "db \<in> set (auxlist_data_in args mt auxlist)"
              using kj_props
              by auto
            then have "mem (args_ivl args) (cur - time db)"
              using time
              unfolding auxlist_data_in_def time_def
              by auto
            moreover have auxlist_idx: "(auxlist_data_in args mt auxlist)!(k+j) = auxlist!(k+j)"
              using data_in_props kj_props(1)
              by auto
            ultimately have "mem (args_ivl args) (cur - time (auxlist!(k+j)))"
              using kj_props(2)
              by auto
            
            then have "tuple \<in> relR (auxlist!(k+j)) \<or>
                (\<exists>j \<in> {(k+j)<..<(length auxlist)}.
                  join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
                )"
              using cond
              by auto
  
            moreover {
              assume "(\<exists>j \<in> {(k+j)<..<(length auxlist)}.
                  join_cond (args_pos args) (relL (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
                )"
              then obtain j' where j'_props:
                "j' \<in> {(k+j)<..<(length auxlist)}"
                "join_cond (args_pos args) (relL (auxlist!j')) (restrict (args_L args) (args_R args) tuple)"
                by blast
  
              then have "j' \<in> A" using A_def j_props by auto
              then have "j' \<le> j" using A_props j_def by auto
              then have "False" using j'_props by auto
            }
  
            ultimately have "tuple \<in> relR (auxlist!(k+j))" by blast
            then have "tuple \<in> relR db" using kj_props auxlist_idx by auto
          }
          then have "(\<forall>(t, l, r) \<in> set suffix.
                tuple \<in> r
              )"
              "join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)"
            using suffix_first
            unfolding relR_def
            by (auto simp add: relR_def case_prod_beta')
          then have "\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
            let suffix = drop n (auxlist_data_in args mt auxlist) in (
              (\<forall>(t, l, r) \<in> set suffix.
                tuple \<in> r
              ) \<and>
              join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)
          )"
            using j_le suffix_def
            by (meson atLeastLessThan_iff less_eq_nat.simps(1))
          then have "(\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
                let suffix = drop n (auxlist_data_in args mt auxlist) in (
                  (\<forall>(t, l, r) \<in> set suffix.
                    tuple \<in> r
                  ) \<and>
                  (
                    join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)
                  )
              )
            )"
            by (auto simp add: Let_def)
          moreover have "length (linearize data_in) = length (auxlist_data_in args mt auxlist)"
          proof -
            have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
              using assms(1)
              unfolding valid_nmtaux_def prod.case by blast
            then show ?thesis
              by (metis length_map)
          qed
          ultimately have "tuple_since_lhs tuple (linearize data_in) args (auxlist_data_in args mt auxlist)"
            using non_empty_alt Queue.is_empty_alt
            unfolding tuple_since_lhs_def 
            by auto
          then have "tuple \<in> since_sat" using assms(1) unfolding valid_nmtaux_def prod.case by blast
          then have "tuple \<in> snd (result_nmtaux args aux)"
            using non_empty_alt
            unfolding aux_def
            by auto
        }
        moreover {
          define j' where "j' = j - length (linearize data_in)"
          assume j_geq: "j \<ge> length (linearize data_in)"
          moreover have data_prev_props: "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
            using assms(1)
            unfolding valid_nmtaux_def prod.case by blast
          ultimately have prev: "auxlist!j = (auxlist_data_prev args mt auxlist)!j'"
            using j_props(1)
            unfolding j'_def
            by auto
          then have idx_shift: "auxlist!j = (linearize data_prev)!j'"
            using data_props(1)
            by auto
          have "j' < length (auxlist_data_prev args mt auxlist)"
            using data_prev_props j_props i_props j_geq
            unfolding j'_def
            by auto
          then have not_mem_0: "\<not>mem (args_ivl args) 0"
            using memL_mono[of "args_ivl args" 0]
            unfolding auxlist_data_prev_def
            by auto
          then have mask_eq: "(args_L args) = (args_R args)"
            using assms(1)
            by (simp add: valid_nmtaux_def)
  
          have data_in_props: "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
            using assms(1)
            unfolding valid_nmtaux_def prod.case by blast
          have "length (linearize data_prev) + length (linearize data_in) =
            length (auxlist_data_prev args mt auxlist) + length (auxlist_data_in args mt auxlist)"
            using data_props
            by (metis length_map)
          also have "\<dots> = length auxlist"
            using data_in_props data_prev_props
            by simp
          finally have "length (linearize data_prev) + length (linearize data_in) = length auxlist" .
          then have j'_le: "j' < length (linearize data_prev)"
            using j_geq j_props(1)
            unfolding j'_def
            by auto
          
          define B where "B = fst ` {
            tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)).
            tuple = snd tas
          }"
          from assms(1) have "newest_tuple_in_mapping fst data_prev tuple_in_once (\<lambda>x. True)"
            unfolding valid_nmtaux_def prod.case by blast
          then have mapping_val: "Mapping.lookup tuple_in_once tuple = safe_max B"
            unfolding newest_tuple_in_mapping_def B_def
            by auto
  
          define t where "t = fst ((linearize data_prev) ! j')"
          define X where "X = snd ((linearize data_prev) ! j')"
          have tuple_eq: "restrict (args_L args) (args_R args) tuple = tuple"
            using mask_eq restrict_idle[OF valid_nmtaux_distinct(2)[OF assms(1)] wf]
            by auto
          have "args_pos args"
            using not_mem_0 assms(1)
            unfolding valid_nmtaux_def prod.case by blast
          then have "restrict (args_L args) (args_R args) tuple \<in> fst X"
            using j_props idx_shift
            unfolding relL_def X_def
            by auto
          moreover have
            "(t, X) \<in> (set (linearize data_prev))"
            using j'_le
            unfolding t_def X_def
            by auto
          ultimately have "(t, restrict (args_L args) (args_R args) tuple) \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev))"
            unfolding ts_tuple_rel_f_def
            by blast
          then have t_mem_B: "t \<in> B"
            unfolding B_def
            using tuple_eq
            by (simp add: image_iff)
          then have B_props: "B \<noteq> {}" "finite B"
            using B_def
            by (auto simp add: finite_fst_ts_tuple_rel)
          then have "safe_max B = Some (Max B)"
            unfolding safe_max_def
            by auto
          then have "Mapping.lookup tuple_in_once tuple = Some (Max B)"
            using mapping_val
            by auto
          then have "tuple \<in> Mapping.keys tuple_in_once"
            by (simp add: Mapping_keys_intro)
          moreover have "tuple_in_once_keys = Mapping.keys tuple_in_once"
            using assms(1)
            unfolding valid_nmtaux_def prod.case by blast
          ultimately have "tuple \<in> snd (result_nmtaux args aux)"
            using non_empty_alt
            unfolding aux_def
            by auto
        }
        ultimately have "tuple \<in> snd (result_nmtaux args aux)" using not_le_imp_less by blast
      }
      ultimately have "tuple \<in> snd (result_nmtaux args aux)" by blast
    }
    then have "snd (trigger_results args cur auxlist) \<subseteq> snd (result_nmtaux args aux)"
      by auto
    then have "snd (trigger_results args cur auxlist) = snd (result_nmtaux args aux)"
      using subset
      by blast
    then have ?thesis using aux_def non_empty_alt by auto
  }
  moreover {
    assume "Queue.is_empty data_in"
    then have ?thesis using data_in_auxlist_nonempty[OF assms(1)] time by auto
  }
  ultimately show ?thesis by blast
qed

lemma valid_result_nmtaux: "valid_nmtaux args cur aux auxlist \<Longrightarrow> result_nmtaux args aux = trigger_results args cur auxlist"
  using valid_result_nmtaux_unfolded
  by (cases aux) (fast)

lemma drop_list_shift: "n \<ge> m \<Longrightarrow> drop n xs = drop (n - m) (drop m xs)"
  by simp

(* analogous to join_mmsaux *)
lemma proj_tuple_in_join_optim_equiv:
  assumes "table R r" "distinct R"
  shows "proj_tuple_in_join_optim pos r R l L = {as \<in> r. proj_tuple_in_join pos L R as l}"
proof -
  have idle: "restrict R R as = as" if "as \<in> r" for as
    using restrict_idle[OF assms(2) tableD[OF assms(1) that]] .
  have nil: "x = []" if "R = []" "x \<in> r" for x
    using idle[OF that(2)] that(1) by simp
  show ?thesis
    by (auto simp: proj_tuple_in_join_def idle dest: nil)
qed

(* TODO: combine with shift_end *)
lemma ts_tuple_rel_empty: "ts_tuple_rel_f (\<lambda>_. {}) A = {}"
  unfolding ts_tuple_rel_f_def
  by auto

lemma Mapping_empty_filter: "Mapping.filter f Mapping.empty = Mapping.empty"
  by (metis Mapping.lookup_empty Mapping_lookup_filter_not_None mapping_eqI)

lemma fold_Mapping_filter_empty: "fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs Mapping.empty = Mapping.empty"
proof (induction xs arbitrary: )
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs Mapping.empty) = Mapping.empty"
    by auto
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs (Mapping.filter (f x Mapping.empty) Mapping.empty)) = Mapping.empty"
    using Mapping_empty_filter[of "f x Mapping.empty"]
    by auto
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs \<circ> (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) x) Mapping.empty = Mapping.empty"
    by auto
  then show ?case by simp
qed

lemma Mapping_filter_Some:
  assumes "Mapping.lookup mapping k = Some v"
  assumes "f k v = True"
  shows "Mapping.lookup (Mapping.filter f mapping) k = Some v"
  using assms
  by (simp add: Mapping_keys_filterI Mapping_lookup_filter_keys)

lemma Mapping_filter_None:
  assumes "Mapping.lookup mapping k = None"
  shows "Mapping.lookup (Mapping.filter f mapping) k = None"
  using assms Mapping_lookup_filter_not_None
  by fastforce

lemma filter_order_inv: "filter f (filter g xs) = filter g (filter f xs)"
  by (metis (mono_tags, lifting) filter_cong filter_filter)

lemma not_memL_imp_memR: "\<not> memL (args_ivl args) t \<Longrightarrow> memR (args_ivl args) t"
proof -
  assume "\<not> memL (args_ivl args) t"
  then have memL: "\<forall>t'\<le>t. \<not>mem (args_ivl args) t'" using memL_mono by auto
  have "(memL (args_ivl args), memR (args_ivl args), bounded (args_ivl args)) \<in> {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
    using Rep_\<I>[of "(args_ivl args)"]
    by (simp add: bounded.rep_eq memL.rep_eq memR.rep_eq)
  then obtain t_ex where t_ex_props: "mem (args_ivl args) t_ex"
    by auto
  {
    assume memR: "\<not>memR (args_ivl args) t"
    {
      fix t'
      assume t'_leq_t: "t' \<ge> t"
      then have "\<not>memR (args_ivl args) t'"
        using memR memR_antimono
        by auto
    }
    then have "\<forall>t'\<ge>t. \<not>mem (args_ivl args) t'" by auto
    then have "\<forall>t'. \<not>mem (args_ivl args) t'"
      using memL nat_le_linear
      by auto
    then have "False" using t_ex_props by auto
  }
  then show "memR (args_ivl args) t" by auto
qed

lemma not_memR_imp_memL: "\<not> memR (args_ivl args) t \<Longrightarrow> memL (args_ivl args) t"
proof -
  assume "\<not> memR (args_ivl args) t"
  then have memR: "\<forall>t'\<ge>t. \<not>memR (args_ivl args) t'" using memR_antimono by auto
  have "(memL (args_ivl args), memR (args_ivl args), bounded (args_ivl args)) \<in> {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
    using Rep_\<I>[of "(args_ivl args)"]
    by (simp add: bounded.rep_eq memL.rep_eq memR.rep_eq)
  then obtain t_ex where t_ex_props: "mem (args_ivl args) t_ex"
    by auto
  {
    assume memL: "\<not>memL (args_ivl args) t"
    {
      fix t'
      assume t'_leq_t: "t' \<le> t"
      then have "\<not>memL (args_ivl args) t'"
        using memL memL_mono
        by auto
    }
    then have "\<forall>t'\<le>t. \<not>mem (args_ivl args) t'" by auto
    then have "\<forall>t'. \<not>mem (args_ivl args) t'"
      using memR nat_le_linear
      by auto
    then have "False" using t_ex_props by auto
  }
  then show "memL (args_ivl args) t" by auto
qed

lemma fold_append_queue_map: "linearize (fold (\<lambda>(t, l, r) q. append_queue (t, r) q) xs q) = linearize q @ (map (\<lambda>(t, l, r). (t, r)) xs)"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

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

lemma mem_mt_and_memR_imp_mem:
  assumes "nt \<ge> mt"
  shows "(mem (args_ivl args) (mt - t) \<and> memR (args_ivl args) (nt - t)) = (mem (args_ivl args) (mt - t) \<and> mem (args_ivl args) (nt - t))"
  using assms by auto

lemma take_filter_mem:
  assumes "\<forall>db \<in> set xs. memR I (mt - time db)"
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
  from Cons(2) have x_memR: "((\<lambda>(t, _). memR I (mt - t)) x)" unfolding time_def by auto
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


lemma fold_alt: "fold f (xs @ [x]) acc = f x (fold f xs acc)"
  by simp

lemma drop_last: "length xs \<ge> 1 \<Longrightarrow> drop (length xs - 1) xs = [last xs]"
  by (cases xs rule: rev_cases) simp_all

lemma filter_sublist: "x#xs = filter f zs \<Longrightarrow> \<exists>n\<le>length zs. xs = filter f (drop n zs) \<and> [x] = filter f (take n zs)"
  proof (induction zs)
    case (Cons z zs)
    then show ?case
    proof (cases "f z")
      case False
      then obtain n where "n\<le>length zs" "xs = filter f (drop n zs)" "[x] = filter f (take n zs)"
        using Cons
        by auto
      then show ?thesis
        using False
        by (auto intro: exI[of _ "n+1"])
    qed (auto intro: exI[of _ 1])
  qed (auto)

lemma idx_filter:
  assumes "x = (filter f xs)!i"
  assumes "i < length (filter f xs)"
  shows "\<exists>i' \<in> {0..<length xs}. xs!i' = x"
  using assms
  by (metis (no_types, lifting) atLeastLessThan_iff in_set_conv_nth
      mem_Collect_eq set_filter zero_le)

lemma idx_filter_pair:
  assumes "x = (filter f xs)!i"
  assumes "y = (filter f xs)!j"
  assumes "j < i" "i < length (filter f xs)"
  shows "\<exists>i' \<in> {0..<length xs}. \<exists>j' \<in> {0..<i'}. xs!j' = y \<and> xs!i' = x"
using assms proof (induction "filter f xs" arbitrary: xs i j)
  case (Cons a as zs)

  obtain i' where i'_def: "i = Suc i'"
    using Cons(5)
    by (cases i) (auto)

  obtain n where zs'_props: "n\<le>length zs" "as = filter f (drop n zs)" "[a] = filter f (take n zs)"
    using Cons filter_sublist[of a as f zs]
    by auto

  show ?case
  proof (cases j)
    case 0

    obtain i'' where i''_props: "i'' \<in> {0..<length (drop n zs)}" "(drop n zs)!i'' = x"
      using idx_filter[of x f "(drop n zs)" i'] Cons(3-)[folded Cons(2)] zs'_props
      by (auto simp add: i'_def)

    have "y = a" using 0 Cons(2)[symmetric] Cons(4) by auto
    then have y_list: "[y] = filter f (take n zs)" using zs'_props(3) by auto
    then have "filter f (take n zs)!0 = y"
      by (metis nth_Cons_0)
    moreover have "0 < length (filter f (take n zs))" using y_list by auto

    ultimately obtain j'' where j''_props: "j'' \<in> {0..<length (take n zs)}" "(take n zs)!j'' = y"
      using idx_filter[of y f "(take n zs)" 0]
      by (auto)

    have "n + i'' \<in> {0..<length zs}" "j'' \<in> {0..<n + i''}" "zs ! j'' = y" "zs ! (n + i'') = x"
      using i''_props j''_props zs'_props(1) by auto
    then show ?thesis by blast
      
  next
    case (Suc j')
    have "x = as ! i'" "y = as ! j'" "j' < i'" "i' < length as"
      using Cons(3-)[folded Cons(2)] Suc i'_def by auto
    then obtain i'' j'' where "i'' < length (drop n zs)" "j'' < i''"
      "drop n zs ! j'' = y" "drop n zs ! i'' = x"
      using Cons(1)[OF zs'_props(2), folded zs'_props(2), of i' j'] by auto
    then have "n + i'' \<in> {0..<length zs}" "n + j'' \<in> {0..<n + i''}"
      "zs ! (n + j'') = y" "zs ! (n + i'') = x"
      using zs'_props(1) by auto
    then show ?thesis by blast
  qed
qed (simp)

lemma no_hist_last_not_sat:
  assumes data_in_len: "length xs + idx_oldest = idx_mid"
  assumes tuple_since_tp: "\<forall>idx. \<not> tuple_since_tp args as xs idx_oldest idx_mid idx"
  assumes non_empty: "xs \<noteq> []"
  shows "as \<notin> snd (last xs)"
proof -
  have idx_props: "\<forall>idx<idx_mid. (
      \<not>(\<forall>(t, r) \<in> set (drop (idx-idx_oldest) xs). 
        as \<in> r
      ) \<or>
      \<not>(idx > idx_oldest \<longrightarrow> as \<notin> (snd (xs!(idx-idx_oldest-1))))
    )"
    using tuple_since_tp non_empty
    unfolding tuple_since_tp_def
    by auto
  {
    define db where "db = last xs"
    define i where "i = length xs - 1"
    assume assm: "as \<in> snd db"
    then have in_len: "length xs > 0"
      using non_empty by auto
    then have db_i: "db = xs!i"
      unfolding db_def i_def
      using last_conv_nth
      by blast
    define A where "A = {j \<in> {0..<length xs}. as \<notin> snd (xs!j)}"
    define j where "j = Max A"
    define idx where "idx = idx_oldest + j + 1"
    {
      define idx where "idx = idx_oldest"
      assume hist: "\<forall>db \<in> set xs. as \<in> snd db"
      have "idx < idx_mid" "\<forall>(t, r) \<in> set (drop (idx-idx_oldest) xs). as \<in> r"
        unfolding idx_def
        using data_in_len in_len hist
        by auto
      moreover have "idx > idx_oldest \<longrightarrow> as \<notin> (snd (xs!(idx-idx_oldest-1)))"
        unfolding idx_def
        by blast
      ultimately have "False"
        using idx_props assm(1)
        by auto
    }
    then obtain db' where db'_props: "db' \<in> set xs" "as \<notin> snd db'" by blast
    then have "\<exists>j. xs!j = db' \<and> j \<in> {0..<length xs}"
      by (meson atLeastLessThan_iff leI not_less0 nth_the_index the_index_bounded)
    then have A_props: "A \<noteq> {}" "finite A"
      unfolding A_def
      using db'_props(2)
      by auto
    then have "j \<in> A"
      unfolding j_def
      by auto
    then have j_props: "j \<in> {0..<length xs}" "as \<notin> snd (xs!j)"
      unfolding A_def
      by auto
    then have j_le_i: "j \<in> {0..<i}"
      using db_i assm
      unfolding i_def
      by (metis One_nat_def Suc_leI Suc_pred atLeastLessThan_iff in_len leD linorder_neqE_nat)
    {
      assume "\<exists>k \<in> {j<..<length xs}. as \<notin> snd (xs!k)"
      then obtain k where k_props: "k \<in> {j<..<length xs}" "as \<notin> snd (xs!k)"
        by auto
      then have "k \<in> A" unfolding A_def by auto
      then have "False" using k_props(1) A_props j_def by auto
    }
    then have suffix_hist: "\<forall>k \<in> {j<..<length xs}. as \<in> snd (xs!k)"
      by blast
    {
      fix db
      assume "db \<in> set (drop (j+1) xs)"
      then obtain k where k_props: "(drop (j+1) xs)!k = db" "k \<in> {0..<length (drop (j+1) xs)}"
        by (meson atLeastLessThan_iff in_set_conv_nth zero_le)
      then have "xs!(k + (j+1)) = db"
        by (simp add: add.commute)
      then have "as \<in> snd db" using suffix_hist
        using k_props(2)
        by auto
    }
    then have "\<forall>db \<in> set (drop (j+1) xs). as \<in> snd db"
      by auto
    then have "\<forall>(t, r) \<in> set (drop (idx-idx_oldest) xs). as \<in> r"
      unfolding idx_def
      by auto
    moreover have "as \<notin> (snd (xs!(idx-idx_oldest-1)))"
      unfolding idx_def
      using j_props(2)
      by auto
    moreover have "idx < idx_mid"
      using data_in_len j_le_i
      unfolding idx_def i_def
      by auto
    ultimately have "False"
      using idx_props assm(1)
      by auto
  }
  then show "as \<notin> snd (last xs)" by auto
qed

lemma idx_append_snd: "i \<in> {length ys..<length xs} \<Longrightarrow> xs = ys @ zs \<Longrightarrow> xs!i = zs!(i - length ys)"
  by (simp add: nth_append)

lemma nth_set_member: "i \<in> {0..<length xs} \<Longrightarrow> xs!i \<in> set xs"
  by auto

lemma tuple_since_hist_lookup_eq:
  assumes "(\<forall>as. (case Mapping.lookup tuple_since_hist as of
    Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx
    | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx)
  )"
  assumes "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid jdx" "jdx > idx_oldest"
  assumes "length (linearize data_in) + idx_oldest = idx_mid"
  shows "Mapping.lookup tuple_since_hist as = Some jdx"
proof -
  (* (idx_oldest + j + 1) = jdx *)
  define j where "j = jdx - idx_oldest - 1"

  from assms(2) have in_nonempty: "linearize data_in \<noteq> []"
    unfolding tuple_since_tp_def
    by auto

  from assms(2-3) have jdx_props: "jdx < idx_mid" "jdx > idx_oldest"
    unfolding tuple_since_tp_def
    by auto
  moreover have "as \<notin> snd ((linearize data_in)!j)"
    using assms(2) jdx_props(2)
    unfolding tuple_since_tp_def j_def
    by auto
  ultimately have j_props: "j \<in> {0..<length (linearize data_in) - 1}" "as \<notin> snd ((linearize data_in)!j)"
    using assms(4)
    unfolding j_def
    by auto

  from assms(2) have all_relR: "(\<forall>(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) (linearize data_in)). as \<in> y)"
    using jdx_props(2)
    unfolding tuple_since_tp_def j_def
    by fastforce

  obtain idx where idx_props:
    "Mapping.lookup tuple_since_hist as = Some idx"
    "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
    using assms(1) assms(2)
    by (auto split: option.splits)
  then have idx_l: "idx < idx_mid"
    unfolding tuple_since_tp_def
    by auto
  {
    assume assm: "idx < (idx_oldest + j + 1)"
    then have j_th: "(linearize data_in)!j = (drop (idx - idx_oldest) (linearize data_in))!(j - (idx - idx_oldest))"
      using idx_props(2) j_props(1) assms(4)
      unfolding tuple_since_tp_def
      by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right add_diff_cancel_left' add_diff_cancel_right' diff_Suc_Suc diff_le_mono le_add_diff_inverse less_imp_le_nat nth_drop)
    have "j - (idx - idx_oldest) < length (drop (idx - idx_oldest) (linearize data_in))"
      using j_props(1) assm by auto
    then have "(linearize data_in)!j \<in> set (drop (idx - idx_oldest) (linearize data_in))"
      unfolding j_th by (rule nth_mem)
    moreover have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest) (linearize data_in)). as \<in> y)"
      using idx_props(2)
      unfolding tuple_since_tp_def
      by auto
    ultimately have "as \<in> snd ((linearize data_in)!j)" by auto
    then have "False" using j_props(2) by auto
  }
  moreover {
    assume assm: "idx > idx_oldest + j + 1"
    then have geq_drop: "idx - idx_oldest - 1 \<ge> j + 1"
      by auto
    moreover have l_len: "(idx - idx_oldest - 1) < length (linearize data_in)"
      using idx_l assms(4) in_nonempty assm
      by linarith
    ultimately have "linearize data_in ! (idx - idx_oldest - 1) = (drop (j + 1) (linearize data_in))!(idx - idx_oldest - 1 - j - 1)"
      by (simp add: Suc_diff_Suc)
    then have "(linearize data_in ! (idx - idx_oldest - 1)) \<in> set (drop (j + 1) (linearize data_in))"
      by (metis (no_types, lifting) l_len geq_drop diff_diff_left diff_less_mono length_drop nth_mem)
    then have "as \<in> snd (linearize data_in ! (idx - idx_oldest - 1))"
      using all_relR
      by auto
    moreover have "as \<notin> snd (linearize data_in ! (idx - idx_oldest - 1))"
      using assm idx_props(2)
      unfolding tuple_since_tp_def
      by auto
    ultimately have "False" by auto
  }
  ultimately have "idx = (idx_oldest + j + 1)"
    using linorder_neqE_nat
    by blast
  then have "idx = jdx"
    using jdx_props
    unfolding j_def
    by auto
  then show ?thesis using idx_props(1) by auto
qed

lemma tuple_since_hist_lookup_leq:
  assumes "(case Mapping.lookup tuple_since_hist as of
    Some idx \<Rightarrow> tuple_since_tp args as lin_data_in idx_oldest idx_mid idx
    | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as lin_data_in idx_oldest idx_mid idx)
  "
  assumes "tuple_since_tp args as lin_data_in idx_oldest idx_mid idx_oldest"
  assumes "length lin_data_in + idx_oldest = idx_mid"
  shows "\<exists>idx. Mapping.lookup tuple_since_hist as = Some idx \<and> idx \<le> idx_oldest"
proof -
  {
    assume assm: "\<not>(\<exists>idx. Mapping.lookup tuple_since_hist as = Some idx \<and> idx \<le> idx_oldest)"
    have "False"
    proof (cases "Mapping.lookup tuple_since_hist as")
      case None
      then show ?thesis
        using assms(1-2)
        by (metis option.simps(4))
    next
      case (Some idx)
      then have "tuple_since_tp args as lin_data_in idx_oldest idx_mid idx"
        using assms(1)
        by (auto split: option.splits)
      moreover have "idx > idx_oldest" using Some assm by auto
      ultimately have
        "idx < idx_mid"
        "idx > idx_oldest"
        "as \<notin> snd (lin_data_in ! (idx - idx_oldest - 1))"
        unfolding tuple_since_tp_def
        by auto
      moreover have "(\<forall>(t, y)\<in>set (lin_data_in). as \<in> y)"
        using assms(2)
        unfolding tuple_since_tp_def
        by auto
      ultimately show ?thesis
        using assms(3)
        by (simp add: case_prod_beta')
    qed
  }
  then show ?thesis by auto
qed

lemma idx_append: "i < length xs \<Longrightarrow> ((xs @ [x])!i) = (xs!i)"
  by (simp add: nth_append)

(* since shift_end only affects data_prev, data_in & tuple_in, explicitly write the conditions out *)
lemma valid_shift_end'_unfolded:
  assumes table_tuple_in: "table V1 (Mapping.keys tuple_in)"
  assumes auxlist_tuples: "ts_tuple_rel_f f1_auxlist (set (filter_auxlist auxlist)) =
    {tas \<in> (ts_tuple_rel_f f1_prev (set (linearize data_prev))) \<union> (ts_tuple_rel_f f1_in (set (linearize data_in))).
    P1 tas}"
  assumes data_prev_props:
    "(\<forall>as \<in> \<Union>((f2 o snd) ` (set (linearize data_prev))). wf_tuple V2 as)"
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> t' \<and> \<not> memL I (cur - t))"
  assumes data_in_props:
    "sorted (map fst (linearize data_in))"
    "(\<forall>t \<in> fst ` set (linearize data_in). t \<le> t' \<and> memL I (cur - t))"
  assumes max_ts_tuple_in: "newest_tuple_in_mapping f3 data_in tuple_in P2"
  assumes nt_mono: "nt \<ge> cur" "t' \<le> nt"
  assumes shift_end_appl: "(data_prev', data_in', discard, tuple_in', tuple_in_keys') 
    = shift_end' I nt f3 (data_prev, data_in, tuple_in, tuple_in_keys)"
  shows
    "table V1 (Mapping.keys tuple_in')"
    "ts_tuple_rel_f f1_auxlist (set (filter (\<lambda>(t, rel). memR I (nt - t)) (filter_auxlist auxlist))) =
    {tas \<in> (ts_tuple_rel_f f1_prev (set (linearize data_prev'))) \<union> (ts_tuple_rel_f f1_in (set (linearize data_in'))).
    P1 tas}"
    "(\<forall>as \<in> \<Union>((f2 o snd) ` (set (linearize data_prev'))). wf_tuple V2 as)"
    "sorted (map fst (linearize data_prev'))"
    "(\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> t' \<and> \<not> memL I (cur - t))"
    "sorted (map fst (linearize data_in'))"
    "(\<forall>t \<in> fst ` set (linearize data_in'). t \<le> t' \<and> mem I (cur - t))"
    "newest_tuple_in_mapping f3 data_in' tuple_in' P2"
    "discard = snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
    "linearize data_in' = filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_in)"
    "tuple_in_keys = Mapping.keys tuple_in \<Longrightarrow> tuple_in_keys' = Mapping.keys tuple_in'"
    "tuple_in' = fold (\<lambda>(t, X) tuple_in. Mapping.filter
    (filter_cond (f3 X) tuple_in t) tuple_in) discard tuple_in"
proof -

  show discard_def: "discard = snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
    using shift_end_appl
    by (auto simp only: shift_end'.simps Let_def snd_def split: prod.splits)

  have data_in'_def: "data_in' = fst (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
    using shift_end_appl
    by (auto simp only: shift_end'.simps Let_def fst_def split: prod.splits)
  have data_prev'_def: "data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev"
    using shift_end_appl takedropWhile_queue_fst[of "(\<lambda>(t, X). \<not> memR I (nt - t))" data_prev]
    by (auto simp only: shift_end'.simps Let_def fst_def split: prod.splits)

  have f_simp: "(\<lambda>a (x, y).
              ((case a of (t, X) \<Rightarrow> \<lambda>tuple_in. Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in) x,
               (case a of (t, X) \<Rightarrow> \<lambda>tuple_in tuple_in_keys. {as \<in> tuple_in_keys. filter_cond' (f3 X) tuple_in t as}) x y)) = 
      (\<lambda>(t, X) (tuple_in, tuple_in_keys). (Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in, {as \<in> tuple_in_keys. filter_cond' (f3 X) tuple_in t as}))"
    by auto

  have in_fold: "(tuple_in', tuple_in_keys') = fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (
        Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
        {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
      )
    ) discard (tuple_in, tuple_in_keys)"
    using shift_end_appl
    by (auto simp only: shift_end'.simps Let_def snd_def split: prod.splits)
  then have "tuple_in' = fst (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (
        Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
        {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
      )
    ) discard (tuple_in, tuple_in_keys))"
    by (metis fstI)
  then show tuple_in'_def: "tuple_in' = fold (\<lambda>(t, X) tuple_in. Mapping.filter
    (filter_cond (f3 X) tuple_in t) tuple_in) discard tuple_in"
    using fold_pair_fst[of "\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in" "\<lambda>(t, X) tuple_in tuple_in_keys. {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}" discard tuple_in tuple_in_keys]
    by (auto simp only: f_simp)
  
  have tuple_in_Some_None: "\<And>as t X. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    (as) \<in> (f3 X) \<Longrightarrow> (t, X) \<in> set discard \<Longrightarrow> Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_Some_None unfolding tuple_in'_def by fastforce
  have tuple_in_Some_Some: "\<And>as t. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    (\<And>X. (t, X) \<in> set discard \<Longrightarrow> (as) \<notin> f3 X) \<Longrightarrow> Mapping.lookup tuple_in' as = Some t"
    using fold_Mapping_filter_Some_Some unfolding tuple_in'_def by force
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_None unfolding tuple_in'_def by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_Some_None tuple_in_Some_Some tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping.in_keysD)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    using data_in_props nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    using data_prev_props nt_mono by auto
  show lin_data_in': "linearize data_in' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_in)"
    unfolding data_in'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F1(1)] thm dropWhile_filter[OF F1(1)] ..
  then have set_lin_data_in': "set (linearize data_in') \<subseteq> set (linearize data_in)"
    by auto
  show sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using sorted_filter data_in_props(1) by auto


  have discard_alt: "discard = filter (\<lambda>(t, X). \<not> memR I (nt - t)) (linearize data_in)"
    unfolding discard_def[unfolded takedropWhile_queue_snd] takeWhile_filter[OF F1(1)] ..
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_prev)"
    unfolding data_prev'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F2(1)] ..
  show sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter data_prev_props(2) by auto


  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')). P2 tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')). P2 tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel_f f3 (set (linearize data_in)).
        P2 tas \<and> as = snd tas} = {}"
        using max_ts_tuple_in
        by (auto simp add: newest_tuple_in_mapping_def dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')).
        P2 tas \<and> as = snd tas} = {}"
        using ts_tuple_rel_mono[OF set_lin_data_in'] by auto
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric] by blast
    next
      
      case (Some t)
      show ?thesis
      proof (cases "\<exists>X. (t, X) \<in> set discard \<and> (as) \<in> f3 X")
        case True
        then obtain X where X_def: "(t, X) \<in> set discard" "(as) \<in> f3 X"
          by auto
        have "\<not> memR I (nt - t)"
          using X_def(1) unfolding discard_alt by simp
        moreover have "\<And>t'. (t', as) \<in> ts_tuple_rel_f f3 (set (linearize data_in)) \<Longrightarrow>
          P2 (t', as) \<Longrightarrow> t' \<le> t"
          using max_ts_tuple_in Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff newest_tuple_in_mapping_def)
        ultimately have "{tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')).
          P2 tas \<and> as = snd tas} = {}"
          unfolding lin_data_in' using ts_tuple_rel_set_filter
          by (fastforce simp add: ts_tuple_rel_f_def memR_antimono)
        then show ?thesis
          unfolding tuple_in_Some_None[OF Some X_def(2,1)]
          using iffD2[OF safe_max_empty, symmetric] by blast
      next
        case False
        then have lookup_Some: "Mapping.lookup tuple_in' as = Some t"
          using tuple_in_Some_Some[OF Some] by auto
        have t_as: "(t, as) \<in> ts_tuple_rel_f f3 (set (linearize data_in))"
          "P2 (t, as)"
          using max_ts_tuple_in Some
          by (auto simp add: newest_tuple_in_mapping_def dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then obtain X where X_def: "as \<in> f3 X" "(t, X) \<in> set (linearize data_in)"
          by (auto simp add: ts_tuple_rel_f_def)
        have "(t, X) \<in> set (linearize data_in')"
          using X_def False unfolding discard_alt lin_data_in' by auto
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')).
          P2 tas \<and> as = snd tas}"
          using t_as(2) X_def(1) by (auto simp add: ts_tuple_rel_f_def image_iff)
        have "\<And>t'. (t', as) \<in> ts_tuple_rel_f f3 (set (linearize data_in)) \<Longrightarrow>
          P2 (t', as) \<Longrightarrow> t' \<le> t"
          using max_ts_tuple_in Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff newest_tuple_in_mapping_def)
        then have "Max (fst ` {tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')).
          P2 tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel, OF _ t_in_fst]
            ts_tuple_rel_mono[OF set_lin_data_in'] by fastforce
        then show ?thesis
          unfolding lookup_Some using t_in_fst by (auto simp add: safe_max_def)
      qed
    qed
  qed

  then show "newest_tuple_in_mapping f3 data_in' tuple_in' P2"
    by (auto simp only: newest_tuple_in_mapping_def id_def)
  show table_in: "table V1 (Mapping.keys tuple_in')"
    using tuple_in'_keys table_tuple_in
    by (auto simp add: table_def)

  show "(\<forall>as \<in> \<Union>((f2 o snd) ` (set (linearize data_prev'))). wf_tuple V2 as)"
    using data_prev_props(1) lin_data_prev'
    by auto

  show
    "(\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> t' \<and> \<not> memL I (cur - t))"
    using lin_data_prev' data_prev_props
    by auto

  show
    "\<forall>t\<in>fst ` set (linearize data_in'). t \<le> t' \<and> mem I (cur - t)"
    using lin_data_in' data_in_props nt_mono
    by auto

  show "ts_tuple_rel_f f1_auxlist (set (filter (\<lambda>(t, rel). memR I (nt - t)) (filter_auxlist auxlist))) =
    {tas \<in> (ts_tuple_rel_f f1_prev (set (linearize data_prev'))) \<union> (ts_tuple_rel_f f1_in (set (linearize data_in'))).
    P1 tas}"
    using auxlist_tuples
    unfolding lin_data_prev' lin_data_in' ts_tuple_rel_Un ts_tuple_rel_filter
    by auto

  {
    define P::"(('a list, ts) mapping \<times> 'a list set) \<Rightarrow> bool" where "P = (\<lambda>(mapping, mapping_keys). mapping_keys = Mapping.keys mapping)"
    assume assm: "tuple_in_keys = Mapping.keys tuple_in"

    have "P (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (
        Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
        {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
      )
    ) discard (tuple_in, tuple_in_keys))"
    proof (induction discard rule: rev_induct)
      case Nil
      then show ?case using assm unfolding P_def by auto
    next
      case (snoc x xs)
      define induct where "induct = (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
        (
          Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
          {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
        )
      ) xs (tuple_in, tuple_in_keys))"
      define mapping where "mapping = fst induct"
      define keys where "keys = snd induct"

      have induct_eq: "induct = (mapping, keys)"
        unfolding mapping_def keys_def
        by auto

      define t where "t = fst x"
      define X where "X = snd x"

      have x_eq: "x = (t, X)"
        unfolding t_def X_def
        by auto

      define goal where "goal = (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
        (
          Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
          {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
        )
      ) (xs @ [x]) (tuple_in, tuple_in_keys))"

      have goal_eq: "goal = (\<lambda>(t, X) (tuple_in, tuple_in_keys).
        (
          Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
          {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
        )
      ) x induct"
        unfolding goal_def induct_def
        by auto
      then have goal_eq: "goal = (
          Mapping.filter (filter_cond (f3 X) mapping t) mapping,
          {as \<in> keys. (filter_cond' (f3 X) mapping t) as}
        )"
        unfolding x_eq induct_eq
        by auto

      have "P induct"
        using snoc
        unfolding induct_def
        by auto
      then have IH: "keys = Mapping.keys mapping"
        unfolding induct_eq P_def
        by auto

      have "{as \<in> keys. (filter_cond' (f3 X) mapping t) as} 
  = Mapping.keys (Mapping.filter (filter_cond (f3 X) mapping t) mapping)"
      proof -
        {
          fix as
          assume "as \<in> {as \<in> keys. (filter_cond' (f3 X) mapping t) as}"
          then have "as \<in> keys" "(filter_cond' (f3 X) mapping t) as"
            by auto
          then obtain v where "Mapping.lookup mapping as = Some v" "(filter_cond' (f3 X) mapping t) as"
            unfolding IH
            by (blast dest: Mapping.in_keysD)
          then have "as \<in> Mapping.keys (Mapping.filter (filter_cond (f3 X) mapping t) mapping)"
            by (rule Mapping_keys_filterI)
        }
        moreover {
          fix as
          assume assm: "as \<in> Mapping.keys (Mapping.filter (filter_cond (f3 X) mapping t) mapping)"
          then have "as \<in> Mapping.keys mapping"
            by (rule subsetD[OF Mapping.keys_filter])
          moreover have "(filter_cond' (f3 X) mapping t) as"
            using assm
            by (metis (mono_tags, lifting) Mapping_lookup_filter_None domIff keys_dom_lookup)
          ultimately have "as \<in> {as \<in> keys. (filter_cond' (f3 X) mapping t) as}"
            unfolding IH[symmetric]
            by auto
        }
        ultimately show ?thesis by blast
      qed
      then have "P goal"
        unfolding P_def goal_eq
        by auto
      then show ?case unfolding goal_def by auto
    qed
    then have "P (tuple_in', tuple_in_keys')"
      unfolding in_fold
      by auto
    then show "tuple_in_keys' = Mapping.keys tuple_in'"
      unfolding P_def
      by auto
  }
qed

lemma valid_update_nmtaux'_unfolded:
  assumes valid_before: "valid_nmtaux args cur
    (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes nt_mono: "nt \<ge> cur"
  assumes "(idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys', tuple_since_hist'', hist_sat'', since_sat'') = update_nmtaux' args nt idx_mid idx_oldest data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat"
  shows
    "table (args_L args) (Mapping.keys tuple_in_once')"
    "table (args_R args) (Mapping.keys tuple_since_hist'')"
    \<comment> \<open>data_prev\<close>
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_R args) as)"
    "auxlist_data_prev args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) = (linearize data_prev')"
    "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
    "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l as)"
    "length (linearize data_prev') + idx_mid' = idx_next"

    "auxlist_data_prev args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) = drop (length (linearize data_in'')) (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)"
    \<comment> \<open>data_in\<close>
    "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in''))). wf_tuple (args_R args) as)"
    "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist))) = ts_tuple_rel (set (linearize data_in''))"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)) = (linearize data_in'')"
    "auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)"
    "length (linearize data_in'') + idx_oldest' = idx_mid'"
    \<comment> \<open>tuple_since_hist\<close>
    "(\<forall>as. (case Mapping.lookup tuple_since_hist'' as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)
    )"
    "(\<forall>tuple. tuple \<in> hist_sat'' \<longleftrightarrow>
      (\<not>Queue.is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r
    ))"
    \<comment> \<open>since_sat\<close>
    "(\<forall>tuple. tuple \<in> since_sat'' \<longrightarrow>
      ((tuple \<in> hist_sat'') \<or> tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)))
    )"
    "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)) \<longrightarrow>
      tuple \<in> since_sat''
    )"
    "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
proof - 
  define shift_res where "shift_res = shift_end'
      (flip_int_less_lower (args_ivl args))
      nt
      fst
      (empty_queue::(ts \<times> 'a list set \<times> 'a list set) queue, data_prev, tuple_in_once, tuple_in_once_keys)"
  define empty_queue' where "empty_queue' = fst shift_res"
  
  have data_prev'_def: "data_prev' = (fst o snd) shift_res"
    using assms(3)
    unfolding shift_res_def
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits) 
  
  define move where "move = (fst o snd o snd) shift_res"
  define move' where "move' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move"

  have tuple_in_once'_def: "tuple_in_once' = (fst o snd o snd o snd) shift_res"
    using assms(3)
    unfolding shift_res_def
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits)

  have tuple_in_once_keys'_def: "tuple_in_once_keys' = (snd o snd o snd o snd) shift_res"
    using assms(3)
    unfolding shift_res_def
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits)

  define data_in' where "data_in' = fst (takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
  define in_drop where "in_drop = snd (takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
  have data_in''_def: "data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' data_in'"
    using assms(3)
    unfolding shift_res_def data_in'_def data_in'_def move'_def move_def
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits)

  then have "data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' (dropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
    unfolding data_in'_def move'_def
    using takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
    by auto

  define drop_prev_len where "drop_prev_len = length move - length move'"

  have idx_mid'_def: "idx_mid' = idx_mid + length move"
    using assms(3)
    unfolding shift_res_def move_def drop_prev_len_def
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits)

  have idx_oldest'_def: "idx_oldest' = idx_oldest + length in_drop + drop_prev_len"
    unfolding shift_res_def in_drop_def drop_prev_len_def move'_def move_def
    using assms(3) takedropWhile_queue_snd[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits)

  have shift_end_res: "(empty_queue', data_prev', move, tuple_in_once', tuple_in_once_keys') = shift_end'
      (flip_int_less_lower (args_ivl args))
      nt
      fst
      (empty_queue::(ts \<times> 'a list set \<times> 'a list set) queue, data_prev, tuple_in_once, tuple_in_once_keys)"
    using empty_queue'_def data_prev'_def move_def tuple_in_once'_def tuple_in_once_keys'_def shift_res_def
    by auto
  define fold_op_f where "fold_op_f = (\<lambda>(t::ts, l::'a list set, r::'a list set) (tuple_since_hist:: ('a list, nat) mapping, hist_sat:: 'a list set, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat         = hist_sat \<inter> r;
          since_sat        = since_sat \<inter> r

      in 
      (
        upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
        hist_sat,
        idx_move+1, 
        since_sat \<union> proj_tuple_in_join_optim (args_pos args) r (args_R args) l (args_L args)
      ) 
    )"

  obtain tuple_since_hist' x hist_sat' since_sat' where fold_tuple_res: "(tuple_since_hist', hist_sat', x, since_sat') = fold fold_op_f move (tuple_since_hist, hist_sat, idx_mid, since_sat)"
    using assms(3)
    unfolding fold_op_f_def move_def shift_res_def
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits)
  then have tuple_since_hist''_def: "tuple_since_hist'' = (if (idx_mid' = idx_oldest') then Mapping.empty else tuple_since_hist')"
    using assms(3) 
    unfolding fold_op_f_def move_def shift_res_def
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits)

  have since_sat''_def: "since_sat'' = (if (idx_mid' = idx_oldest') then {} else since_sat')"
    using assms(3) fold_tuple_res
    unfolding fold_op_f_def move_def shift_res_def
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits)

  have hist_sat''_def: "hist_sat'' = (case fst (safe_hd data_in'')
    of None \<Rightarrow>
      {} 
    | Some db \<Rightarrow>
      hist_sat' \<union> {tuple \<in> (snd db).
        case (Mapping.lookup tuple_since_hist'' tuple) of
          Some idx \<Rightarrow> idx \<le> idx_oldest'
         | None \<Rightarrow> False
      })"
    using assms(3) fold_tuple_res
    unfolding fold_op_f_def move_def shift_res_def
    by (auto simp only: update_nmtaux'_def Let_def fst_def snd_def o_def split: prod.splits)

  from assms(1) have table_tuple_in: "table (args_L args) (Mapping.keys tuple_in_once)"
    unfolding valid_nmtaux_def prod.case by blast

  from assms(1) have time: "cur = mt" unfolding valid_nmtaux_def prod.case by blast

  have auxlist_tuples_lhs: "ts_tuple_rel_f (\<lambda>_. {}) (set ((auxlist_data_prev args mt) auxlist)) =
    {tas \<in> (ts_tuple_rel_f (\<lambda>_. {}) (set (linearize empty_queue))) \<union> (ts_tuple_rel_binary_lhs (set (linearize data_prev))).
    False}"
    using ts_tuple_rel_empty
    by auto

  (* ts_tuple_rel_binary_lhs (set (auxlist_data_prev args mt auxlist)) =
    {tas \<in> ts_tuple_rel_binary_lhs (set (linearize empty_queue)) \<union> ts_tuple_rel_f (\<lambda>_. {}) (set (linearize data_prev)). valid_tuple tuple_in_once tas}*)

  from assms(1) have
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_R args) as)"
    by (auto simp only: valid_nmtaux_def)

  moreover have "sorted (map fst (linearize data_prev))"
    using data_sorted[OF assms(1)]
    by auto

  moreover have "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> \<not> memL (args_ivl args) (cur - t))"
    using data_prev_ts_props[OF assms(1)] nt_mono time
    by auto
  ultimately have
    (*"(\<forall>as \<in> \<Union>(relL ` (set (linearize data_prev))). wf_tuple (args_L args) as)"
    "(\<forall>as \<in> \<Union>(relR ` (set (linearize data_prev))). wf_tuple (args_R args) as)"*)
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> \<not> memL (args_ivl args) (cur - t))"
    by auto
  then have data_prev_props:
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> memL (flip_int_less_lower (args_ivl args)) (cur - t))"
    using flip_int_less_lower_memL
    by auto
  
  have data_in_props:
    "sorted (map fst (linearize data_in))"
    "(\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> memL (args_ivl args) (cur - t))"
    using data_sorted[OF assms(1)] data_in_ts_props[OF assms(1)] nt_mono time
    by auto

  have empty_queue_props:
    "(\<forall>as \<in> \<Union>((fst o snd) ` (set (linearize empty_queue))). wf_tuple (args_L args) as)"
    "(\<forall>as \<in> \<Union>((snd o snd) ` (set (linearize empty_queue))). wf_tuple (args_R args) as)"
    "sorted (map fst (linearize empty_queue))"
    "(\<forall>t \<in> fst ` set (linearize empty_queue). t \<le> nt \<and> \<not> memL (flip_int_less_lower (args_ivl args)) (cur - t))"
    by (auto simp add: empty_queue_rep)

  from assms(1) have max_ts_tuple_in:
    "newest_tuple_in_mapping fst data_prev tuple_in_once (\<lambda>x. True)"
    unfolding valid_nmtaux_def prod.case by blast

  have nt_mono: "nt \<ge> cur" "nt \<le> nt" using nt_mono by auto
  have shift_end_props:
    "table (args_L args) (Mapping.keys tuple_in_once')"
    "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
    "sorted (map fst (linearize data_prev'))"
    "\<forall>t\<in>fst ` set (linearize data_prev'). t \<le> nt \<and> mem (flip_int_less_lower (args_ivl args)) (cur - t)"
    "move = snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR (flip_int_less_lower (args_ivl args)) (nt - t)) data_prev)"
    "linearize data_prev' = filter (\<lambda>(t, X). memR (flip_int_less_lower (args_ivl args)) (nt - t)) (linearize data_prev)"
    "tuple_in_once' =
    fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in) move tuple_in_once"
    "tuple_in_once_keys = Mapping.keys tuple_in_once \<Longrightarrow> tuple_in_once_keys' = Mapping.keys tuple_in_once'"
    unfolding relL_def relR_def
    using valid_shift_end'_unfolded [of
        "(args_L args)" tuple_in_once "(\<lambda>_. {})" "(auxlist_data_prev args mt)" auxlist
        "(\<lambda>_. {})" empty_queue fst data_prev "(\<lambda>db. False)" fst "(args_L args)"
        nt "flip_int_less_lower (args_ivl args)" cur fst "(\<lambda>x. True)" nt empty_queue' data_prev' move tuple_in_once',
        OF table_tuple_in auxlist_tuples_lhs empty_queue_props(1, 3-4) 
        data_prev_props max_ts_tuple_in nt_mono shift_end_res
      ]
    by blast+

  show
    "table (args_L args) (Mapping.keys tuple_in_once')"
    "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
    using shift_end_props(1,2)
    by auto

  have "tuple_in_once_keys = Mapping.keys tuple_in_once"
    using assms(1)
    unfolding valid_nmtaux_def prod.case by blast
  then show "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
    using shift_end_props(8)
    by auto

  from assms(1) have auxlist_prev: "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    unfolding valid_nmtaux_def prod.case by blast

  {
    assume "mem (args_ivl args) 0"
    then have "(linearize data_prev) = []"
      using auxlist_prev memL_mono
      unfolding auxlist_data_prev_def
      by auto
    moreover have empty: "linearize data_prev' = []"
      using shift_end_props(6) calculation(1)
      by auto
    ultimately have "(linearize data_prev) = (linearize data_prev')" "(linearize data_prev) = []"  by auto
  }
  then have data_prev_eq_mem_0: "mem (args_ivl args) 0 \<longrightarrow> (linearize data_prev) = (linearize data_prev') \<and> (linearize data_prev) = []"
    by blast

  
  have data_prev'_eq: "linearize data_prev' = filter (\<lambda>(t, X). \<not>memL (args_ivl args) (nt - t)) (linearize data_prev)"
  proof (cases "mem (args_ivl args) 0")
    case True
    then show ?thesis
      using data_prev_eq_mem_0
      by auto
  next
    case False
    then have not_mem: "\<not> memL (args_ivl args) 0" by auto
    show ?thesis
      using shift_end_props(6) flip_int_less_lower_memR[OF not_mem]
      by auto
  qed

  have move_def: "move = snd (takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev)"
  proof (cases "mem (args_ivl args) 0")
    case True
    then show ?thesis
      using shift_end_props(5) data_prev_eq_mem_0
      by (metis takeWhile.simps(1) takedropWhile_queue_snd)
  next
    case False
    then have not_mem: "\<not> memL (args_ivl args) 0" by auto
    then show ?thesis
      using shift_end_props(5) flip_int_less_lower_memR[OF not_mem]
      by auto
  qed
  then have move_takeWhile: "move = takeWhile (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)"
    using takedropWhile_queue_snd
    by auto
  then have move_filter: "move = filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)"
    using data_sorted[OF assms(1)] sorted_filter_takeWhile_memL[of "linearize data_prev" args nt]
    by auto
  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t,_). (memL (args_ivl args) (nt - t)) \<and> (memR (args_ivl args) (nt - t)))"
    by auto
  have move'_eq: "move' = filter (\<lambda>(t,_). memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t)) (linearize data_prev)"
    using move'_def move_filter filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by (auto simp add: filter_simp)

  have filter_data_prev_nt: "filter (\<lambda>(t, _). \<not>memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist) = (linearize data_prev')"
    using auxlist_prev data_prev'_eq
    by auto
  then have auxlist_prev_eq: "(filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (nt - t))) auxlist) = (linearize data_prev')"
    unfolding auxlist_data_prev_def
    using filter_filter[of "(\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t))" "(\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t))" auxlist]
    by auto
  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (nt - t))) = (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t) \<and>  \<not> memL (args_ivl args) (nt - t))"
    by auto
  have filter_and: "(filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t) \<and>  \<not> memL (args_ivl args) (nt - t)) auxlist) = (linearize data_prev')"
    using auxlist_prev_eq
    by (simp add: filter_simp)
  moreover have not_memL_nt_mt: "\<forall>t. (\<not> memL (args_ivl args) (mt - t) \<and>  \<not> memL (args_ivl args) (nt - t)) = (\<not> memL (args_ivl args) (nt - t))"
    using nt_mono time memL_mono[of "args_ivl args"]
    by auto
  ultimately have filter_auxlist_data_prev': "filter (\<lambda>(t, X). \<not>memL (args_ivl args) (nt - t)) auxlist = (linearize data_prev')"
    by auto
  moreover have "\<forall>t. \<not>memL (args_ivl args) (nt - t) = (\<not>memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t))"
    using not_memL_imp_memR[of args]
    by auto
  ultimately have filter_eq: "filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (nt - t))) auxlist = (linearize data_prev')"
  proof -
    have memR_eq: "(memR (args_ivl args) (nt - t) \<and> \<not> memL (args_ivl args) (nt - t)) \<longleftrightarrow> \<not> memL (args_ivl args) (nt - t)" for t
      using not_memL_imp_memR[of args "nt - t"]
      by blast
    show ?thesis
      using filter_auxlist_data_prev'
      by (simp add: case_prod_unfold memR_eq)
  qed
  then show auxlist_prev_eq: "auxlist_data_prev args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = (linearize data_prev')"
    unfolding auxlist_data_prev_def
    using filter_filter[of "(\<lambda>(t, _). \<not>memL (args_ivl args) (nt - t))" "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" auxlist]
    by auto

  have filter_data_prev_nt: "filter (\<lambda>(t, rel). \<not> memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist) = auxlist_data_prev args nt auxlist"
    using filter_data_prev_nt filter_auxlist_data_prev'
    unfolding auxlist_data_prev_def
    by auto

  have "\<forall>t. \<not>memL (args_ivl args) (nt - t) = (\<not>memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t))"
    using not_memL_imp_memR[of args]
    by auto
  then have auxlist_data_prev_inv: "auxlist_data_prev args nt auxlist = auxlist_data_prev args nt (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
    unfolding auxlist_data_prev_def filter_filter
    by (simp add: filter_eq filter_auxlist_data_prev')

  {
    assume assm: "mem (args_ivl args) 0"
    then have tuple_in_once_empty: "tuple_in_once = Mapping.empty" using tuple_in_once_mem0[OF assms(1)] by auto
    have filter_simp:"(\<lambda>el tuple_in. Mapping.filter ((case el of (t, X) \<Rightarrow> \<lambda>tuple_in. filter_cond (fst X) tuple_in t) tuple_in) tuple_in) =
      (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)"
      by auto
    have "fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)
   (snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR (flip_int_less_lower (args_ivl args)) (nt - t)) data_prev)) Mapping.empty = Mapping.empty"
      (* Mapping.filter (filter_cond_r (fst X) (proj_tuple maskL) tuple_in t) *)
      using 
        fold_Mapping_filter_empty[of
          "\<lambda>(t, X) tuple_in. (filter_cond (fst X) tuple_in t)"
          "(snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR (flip_int_less_lower (args_ivl args)) (nt - t)) data_prev))"]
      by (auto simp only: filter_simp)
   
    then have "tuple_in_once' = Mapping.empty" "tuple_in_once = Mapping.empty"
      using tuple_in_once_empty shift_end_props(5) shift_end_props(7)
      by auto
  }
  then have mem0: "mem (args_ivl args) 0 \<Longrightarrow> tuple_in_once = Mapping.empty \<and> tuple_in_once' = Mapping.empty"
    by auto

  {
    assume "\<not>mem (args_ivl args) 0"
    then have False: "\<not>memL (args_ivl args) 0" by auto

    have "tuple_in_once' = fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)
        move tuple_in_once"
      using shift_end_props(7)
      by auto
    then have tuple_in_once'_eq: "tuple_in_once' = fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)
      (snd (takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev)) tuple_in_once"
      unfolding move_def
      using flip_int_less_lower_memR[OF False]
      by auto
    define fold_fn :: "(nat \<times> 'a list set \<times> 'a list set) \<Rightarrow> ('a list, nat) mapping \<Rightarrow> ('a list, nat) mapping"
      where "fold_fn = (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)"
    define fold_list where "fold_list = (snd (takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev))"
    then have tuple_in_once'_eq: "tuple_in_once' = fold fold_fn fold_list tuple_in_once"
      using tuple_in_once'_eq
      unfolding fold_fn_def fold_list_def
      by simp

    from fold_list_def have fold_list_props: "\<forall>(t, X) \<in> set fold_list. memL (args_ivl args) (nt - t)"
      using takedropWhile_queue_snd[of "(\<lambda>(t, X). memL (args_ivl args) (nt - t))" data_prev]
      set_takeWhileD
      unfolding fold_list_def
      by fastforce

    {
      fix tuple
      assume t'_props: "Mapping.lookup tuple_in_once tuple = None"     
      then have "Mapping.lookup (fold fold_fn fold_list tuple_in_once) tuple = None"
        using fold_Mapping_filter_None[of tuple_in_once tuple fst fold_list]
        unfolding fold_fn_def
        by auto
      then have "Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
        using tuple_in_once'_eq t'_props
        by auto
    }
    then have none: "\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      by auto

    {
      fix t tuple
      assume t_props: "Mapping.lookup tuple_in_once tuple = Some t" "memL (args_ivl args) (nt - t)"
      from assms(1) have "(\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l as)"
        unfolding valid_nmtaux_def prod.case by blast
      moreover have "tuple \<in> Mapping.keys tuple_in_once"
        using t_props(1)
        by (simp add: Mapping_keys_intro)
      ultimately have "\<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l tuple"
        using t_props(1)
        by fastforce
      then obtain X where X_props: "(t, X) \<in> set (linearize data_prev)" "join_cond (args_pos args) (fst X) tuple"
        by auto
      moreover have
        "(\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args)"
        "auxlist_data_prev args mt auxlist = (linearize data_prev)"
        using assms(1)
        unfolding valid_nmtaux_def prod.case by blast+
      ultimately have pos: "args_pos args"
        using memL_mono[of "args_ivl args" "0"]
        unfolding auxlist_data_prev_def
        by auto

      obtain i where i_props: "i \<in> {0..<length (linearize data_prev)}" "(linearize data_prev)!i = (t, X)"
        using X_props
        by (meson atLeastLessThan_iff leI not_less0 nth_the_index the_index_bounded)
      {
        assume assm: "(t, X) \<notin> set (takeWhile (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev))"
        then have "\<exists>j. j<i \<and> \<not>((\<lambda>(t, X). memL (args_ivl args) (nt - t)) ((linearize data_prev)!j))"
        proof -
          have f1: "i = length (takeWhile (\<lambda>(n, p). memL (args_ivl args) (nt - n)) (linearize data_prev)) \<or> length (takeWhile (\<lambda>(n, p). memL (args_ivl args) (nt - n)) (linearize data_prev)) < i"
            using assm i_props(2)
            by (metis (no_types) in_set_conv_nth linorder_neqE_nat takeWhile_nth)
          have "length (takeWhile (\<lambda>(n, p). memL (args_ivl args) (nt - n)) (linearize data_prev)) < length (linearize data_prev)"
            using X_props(1) assm
            by (metis (no_types) length_takeWhile_less takeWhile_eq_all_conv)
          then show ?thesis
            using f1 i_props(2) t_props(2) nth_length_takeWhile
            by fastforce
        qed
        then obtain j where j_props: "j<i" "\<not>memL (args_ivl args) (nt - (fst ((linearize data_prev)!j)))"
          by fastforce
        moreover have "fst ((linearize data_prev)!j) \<le> fst ((linearize data_prev)!i)"
          using i_props(1) j_props(1) sorted_nth_mono[OF data_sorted(1)[OF assms(1)], of j i]
          by simp
        ultimately have "\<not>memL (args_ivl args) (nt - (fst ((linearize data_prev)!i)))"
          using j_props memL_mono
          by auto
        then have "False" using i_props t_props by auto
      }
      then have "(t, X) \<in> set (takeWhile (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev))"
        using t_props(2)
        by auto
      then have "(t, X) \<in> set fold_list"
        unfolding fold_list_def
        using takedropWhile_queue_snd[of "(\<lambda>(t, X). memL (args_ivl args) (nt - t))" data_prev]
        by auto
      moreover have "tuple \<in> fst X"
      proof -
        show ?thesis 
          using X_props(2) pos
          by auto
      qed
      ultimately have "Mapping.lookup (fold fold_fn fold_list tuple_in_once) tuple = None"
        using fold_Mapping_filter_Some_None[of tuple_in_once tuple t fst _ fold_list] t_props(1) X_props(2)
        unfolding fold_fn_def
        by auto
      then have "Mapping.lookup tuple_in_once' tuple = None"
        using tuple_in_once'_eq
        by auto
    }
    then have Some_none:
      "\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None"
      by auto

    {
      fix t tuple
      assume t_props: "Mapping.lookup tuple_in_once tuple = Some t" "\<not>memL (args_ivl args) (nt - t)"
      {
        fix X
        assume "(t, X) \<in> set fold_list"
        then have "memL (args_ivl args) (nt - t)"
          using fold_list_props
          by auto
        then have "False" using t_props by auto
      }
      then have "(\<And>X. (t, X) \<in> set fold_list \<Longrightarrow> tuple \<notin> fst X)" by auto
      moreover have "Mapping.lookup tuple_in_once tuple = Some t" using t_props by auto
      ultimately have "Mapping.lookup (fold fold_fn fold_list tuple_in_once) tuple = Mapping.lookup tuple_in_once tuple"
        using fold_Mapping_filter_Some_Some[of tuple_in_once tuple t fold_list fst]
        unfolding fold_fn_def
        by auto
      then have "Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
        using tuple_in_once'_eq
        by auto
    }
    then have tuple_in_once_eq_Some:
      "\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> \<not> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      "\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None"
      "\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      using none Some_none
      by auto
  }
  then have
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t  \<and> \<not> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    by auto

  moreover {
    assume "mem (args_ivl args) 0"
    then have "\<forall>tuple. Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      using mem0
      by auto
  }
  ultimately have tuple_in_once_lookup:
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t  \<and> \<not> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    "mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    by auto

  have tuple_in_once'_subseteq: "Mapping.keys tuple_in_once' \<subseteq> Mapping.keys tuple_in_once"
  proof (cases "mem (args_ivl args) 0")
  case True
    then show ?thesis using mem0 by blast
  next
    case False
    {
      fix k
      assume "k \<in> Mapping.keys tuple_in_once'"
      then have "k \<in> Mapping.keys tuple_in_once"
        using False tuple_in_once_lookup(3)
        by (metis domIff keys_dom_lookup)
    }
    then show ?thesis by auto
  qed

  from assms(1) have data_prev_wf:
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_R args) as)"
    by (auto simp only: valid_nmtaux_def)

  then show
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_R args) as)"
    using shift_end_props(6)
    by auto

  from assms(1) have tuple_in_once_props:
    "(\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l as)"
    unfolding valid_nmtaux_def prod.case by blast
  {
    fix as t
    assume assm: "Mapping.lookup tuple_in_once' as = Some t"
    then have "\<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l as"
    proof (cases "mem (args_ivl args) 0")
      case True
      then show ?thesis
        using assm mem0
        by simp
    next
      case False
      from assm have "as \<in> Mapping.keys tuple_in_once'"
        by (simp add: Mapping_keys_intro)
      then have as_mem: "as \<in> Mapping.keys tuple_in_once"
        using assm tuple_in_once'_subseteq
        by auto
      then obtain t' where t'_props: "Mapping.lookup tuple_in_once as = Some t'"
        using Mapping.in_keysD[of as tuple_in_once]
        by auto
      show ?thesis
      proof (cases "memL (args_ivl args) (nt - t')")
        case True
        then have "Mapping.lookup tuple_in_once' as = None"
          using False t'_props tuple_in_once_lookup(2)
          by auto
        then show ?thesis using assm by auto
      next
        case not_memL: False
        then have "Mapping.lookup tuple_in_once' as = Some t'"
          using False t'_props tuple_in_once_lookup(1)
          by auto
        then have t_eq: "t=t'" "Mapping.lookup tuple_in_once as = Some t"
          using assm t'_props
          by auto
        then obtain l r where tlr_props: "(t, l, r) \<in> set (linearize data_prev)" "(join_cond (args_pos args) l as)"
          using as_mem tuple_in_once_props
          by fastforce
        then have "(t, l, r) \<in> set (linearize data_prev')"
          using False not_memL data_prev'_eq t_eq(1)
          by auto
        then show ?thesis
          using tlr_props
          by auto
      qed
    qed
  }
  then show "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l as)"
    using Mapping.in_keysD
    by fastforce

  have filter_simp: "(\<lambda>(t, _). mem (args_ivl args) (nt - t)) = (\<lambda>x. (case x of (t, _) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t)))" by auto
  have "drop_prev_len = length (filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    unfolding drop_prev_len_def move_filter move'_eq
    by auto
  then have "drop_prev_len = length (filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) (linearize data_prev))"
    by (auto simp add: filter_simp)
  then have "drop_prev_len = length (filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by auto
  moreover have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) =
    length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))) +
    length (filter (\<lambda>x. \<not> (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t))) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)"]
    by auto
  ultimately have "drop_prev_len = length (filter (\<lambda>x. \<not> (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t))) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    by auto
  then have "drop_prev_len = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    by (simp add: case_prod_beta')
  then have "drop_prev_len = length (filter (\<lambda>x. (case x of (t, _) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> \<not> memR (args_ivl args) (nt - t))) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by auto
  then have "drop_prev_len = length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    by (simp add: case_prod_beta')
  moreover have "\<forall>t. (memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) = (\<not> memR (args_ivl args) (nt - t))"
    using not_memR_imp_memL[of args]
    by auto
  ultimately have drop_prev_len_eq: "drop_prev_len = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto

  from assms(1) have data_prev_len: "length (linearize data_prev) + idx_mid = idx_next" unfolding valid_nmtaux_def prod.case by blast

  have "length (linearize data_prev') = length (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using data_prev'_eq
    by auto
  then have lin_prev'_len: "length (linearize data_prev') = length (filter (\<lambda>x. \<not> (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t))) (linearize data_prev))"
    by (metis (mono_tags, lifting) case_prod_beta' filter_cong)
  
  have idx_mid'_eq: "idx_mid' = idx_mid + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using idx_mid'_def move_filter
    by blast

  then have "idx_mid' - idx_mid = length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto

  then have "length (linearize data_prev') + (idx_mid' - idx_mid) = length (linearize data_prev)"
    using lin_prev'_len sum_length_filter_compl[of "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by auto
  
  then show "length (linearize data_prev') + idx_mid' = idx_next"
    using data_prev_len
    by (auto simp add: idx_mid'_def)

  from assms(1) have data_in_len: "length (linearize data_in) + idx_oldest = idx_mid" unfolding valid_nmtaux_def prod.case by blast
  then have mid_geq_old: "idx_mid \<ge> idx_oldest" by auto

  have idx_oldest'_eq: "idx_oldest' = idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + drop_prev_len"
    using idx_oldest'_def
    unfolding in_drop_def
    using takedropWhile_queue_snd[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
      data_sorted[OF assms(1)] sorted_filter_takeWhile_not_memR[of "linearize data_in" args nt]
    by auto
  then have "idx_mid' + idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + drop_prev_len = idx_oldest' + idx_mid + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using idx_mid'_eq
    by auto
  then have len_eq: "idx_mid' + idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + drop_prev_len = idx_oldest' + idx_mid + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto
  have "(\<forall>x. (\<not> memR (args_ivl args) (fst x)) \<longrightarrow> (memL (args_ivl args) (fst x)))"
    using not_memR_imp_memL[of args]
    by auto
  then have prev_not_memR_leq_prev_memL: "length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)) \<le> length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_imp[of "\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)" "\<lambda>(t, _). memL (args_ivl args) (nt - t)" "linearize data_prev"]
    by auto
  have "idx_oldest' \<le> idx_mid + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    unfolding idx_oldest'_eq drop_prev_len_eq
    using data_in_len
    by auto
  then have mid'_geq_old': "idx_oldest' \<le> idx_mid'"
    unfolding idx_mid'_eq
    using prev_not_memR_leq_prev_memL
    by auto

  have "linearize data_in'' = linearize data_in' @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move)"
    using data_in''_def fold_append_queue_map[of move' data_in'] move'_def
    by auto
  then have "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    using data_in'_def takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
          data_sorted[OF assms(1)]
          dropWhile_queue_rep[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
          sorted_filter_dropWhile_memR[of "linearize data_in" args nt] move_def
          takedropWhile_queue_snd[of "(\<lambda>(t, X). memL (args_ivl args) (nt - t))" data_prev]
          sorted_filter_takeWhile_memL[of "linearize data_prev" args nt]
    by auto
  moreover have "filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) (linearize data_prev) = filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev)"
    by (simp add: case_prod_beta')
  ultimately have lin_data_in''_eq: "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by auto
  then have "length (linearize data_in'') = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by auto
  then have "length (linearize data_in'') + length (filter (\<lambda>x. \<not> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) (linearize data_in)) = length (linearize data_in) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(linearize data_in)"]
    by auto
  then have data_in''_len: "length (linearize data_in'') + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by (auto simp add: case_prod_beta')

  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t))"
    by auto

  have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))) + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)"]
          filter_filter[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by (auto simp add: case_prod_beta')
  moreover have "\<forall>t. (memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) = (\<not> memR (args_ivl args) (nt - t))"
    using not_memR_imp_memL[of args]
    by auto
  ultimately have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))) + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto
  then have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t)) (linearize data_prev)) + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by (auto simp add: filter_simp)
  then have len_simp: "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto
  have "idx_mid' + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)) + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + idx_oldest' + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using len_eq idx_mid'_eq data_in_len drop_prev_len_eq
    by auto
  then have "idx_mid' + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + idx_oldest' + (length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)))"
    using prev_not_memR_leq_prev_memL
    by auto
  then have "idx_mid' + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + idx_oldest' + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by (auto simp only: len_simp)
  then show data_in''_len': "length (linearize data_in'') + idx_oldest' = idx_mid'"
    using data_in''_len
    by auto
  then have tuple_since_hist''_def: "tuple_since_hist'' = (if (Queue.is_empty data_in'') then Mapping.empty else tuple_since_hist')"
    using tuple_since_hist''_def Queue.is_empty_alt[of data_in'']
    by auto

  from assms(1) have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in))). wf_tuple (args_R args) as)"
    unfolding valid_nmtaux_def prod.case by blast
  moreover have "(\<forall>as \<in> \<Union>((snd) ` (set (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))))). wf_tuple (args_R args) as)"
    using data_prev_wf(2)
    unfolding relR_def
    by auto
  ultimately show "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in''))). wf_tuple (args_R args) as)"
    unfolding lin_data_in''_eq
    by auto

  have filter_simp: "(\<lambda>x. (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> mem (args_ivl args) (nt - t))) = (\<lambda>(t, _, _). mem (args_ivl args) (nt - t))"
    by auto
  have data_in_auxlist_filter_eq: "auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) = auxlist_data_in args nt auxlist"
    unfolding auxlist_data_in_def filter_filter
    by (simp add: filter_simp)

  {
    fix timed_tuple
    assume assm: "timed_tuple \<in> ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist))"
    define t where "t = fst timed_tuple"
    define tuple where "tuple = snd timed_tuple"
    from assm obtain l r where l_r_def: "tuple \<in> r" "(t, l, r) \<in> set (filter (\<lambda>(t, _, _). mem (args_ivl args) (nt - t)) auxlist)"
      unfolding ts_tuple_rel_f_def t_def tuple_def auxlist_data_in_def
      by auto
    then have mem: "mem (args_ivl args) (nt - t)" "(t, l, r) \<in> set auxlist" by auto
    then have "timed_tuple \<in> ts_tuple_rel (set (linearize data_in''))"
    proof (cases "memL (args_ivl args) (mt - t)")
      case True
      then have "(t, r) \<in> set (linearize data_in)"
        using mem(2) auxlist_mem_or[OF assms(1), of "(t, l, r)"]
        unfolding time_def
        by auto
      then have "(t, r) \<in> set (linearize data_in'')"
        unfolding lin_data_in''_eq
        using mem(1)
        by auto
      then show ?thesis
        using l_r_def(1)
        unfolding ts_tuple_rel_f_def t_def tuple_def
        by fastforce
    next
      case False
      then have "(t, l, r) \<in> set (linearize data_prev)"
        using mem(2) auxlist_mem_or[OF assms(1), of "(t, l, r)"]
        unfolding time_def
        by auto
      then have "(t, l, r) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
        using mem(1)
        by auto
      then have "(t, r) \<in> set (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev)))"
        by force
      then have "(t, r) \<in> set (linearize data_in'')"
        unfolding lin_data_in''_eq
        by auto
      then show ?thesis
        using l_r_def(1)
        unfolding ts_tuple_rel_f_def t_def tuple_def
        by fastforce
    qed
  }
  moreover {
    fix timed_tuple
    assume assm: "timed_tuple \<in> ts_tuple_rel (set (linearize data_in''))"
    define t where "t = fst timed_tuple"
    define tuple where "tuple = snd timed_tuple"

    from assm obtain r where tuple_props: "tuple \<in> r" "(t, r) \<in> (set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @
                  map (\<lambda>(t, l, y). (t, y)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))))"
      unfolding ts_tuple_rel_f_def lin_data_in''_eq t_def tuple_def
      by force
    then have "(t, r) \<in> (set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))) \<or> (t, r) \<in> set (map (\<lambda>(t, l, y). (t, y)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev)))"
      by auto
    moreover {
      assume "(t, r) \<in> (set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)))"
      then have memR: "memR (args_ivl args) (nt - t)" "(t, r) \<in> set (linearize data_in)"
        by auto
      then have "memL (args_ivl args) (mt - t)" using data_in_mem[OF assms(1), of "(t, r)"] by auto
      then have "memL (args_ivl args) (nt - t)" using memL_mono nt_mono time by auto
      then have mem: "mem (args_ivl args) (nt - t)" using memR by auto
      have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
        using assms(1) unfolding valid_nmtaux_def prod.case by blast
      then have "(t, r) \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
        using memR(2)
        by auto
      then obtain l where "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
        using memR(2)
        by auto
      then have "(t, l, r) \<in> set auxlist"
        unfolding auxlist_data_in_def
        by auto
      then have "(t, l, r) \<in> set (auxlist_data_in args nt auxlist)"
        unfolding auxlist_data_in_def
        using mem
        by auto
      then have "timed_tuple \<in> ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist))"
        unfolding ts_tuple_rel_f_def auxlist_data_in_def
        using tuple_props(1) t_def tuple_def
        by fastforce
    }
    moreover {
      assume "(t, r) \<in> set (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev)))"
      then obtain l where "(t, l, r) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
        by auto
      then have mem: "mem (args_ivl args) (nt - t)" "(t, l, r) \<in> set (linearize data_prev)" by auto
      moreover have "auxlist_data_prev args mt auxlist = (linearize data_prev)" using assms(1) unfolding valid_nmtaux_def prod.case by blast
      ultimately have "(t, l, r) \<in> set (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)"
        unfolding auxlist_data_prev_def
        by auto
      then have "(t, l, r) \<in> set auxlist" by auto
      then have "(t, l, r) \<in> set (auxlist_data_in args nt auxlist)"
        unfolding auxlist_data_in_def
        using mem
        by auto
      then have "timed_tuple \<in> ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist))"
        unfolding ts_tuple_rel_f_def auxlist_data_in_def
        using tuple_props(1) t_def tuple_def
        by fastforce
    }
    ultimately have "timed_tuple \<in> ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist))"
      by blast
  }
  ultimately have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist)) = ts_tuple_rel (set (linearize data_in''))"
    by blast
  then show "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist))) = ts_tuple_rel (set (linearize data_in''))"
    using data_in_auxlist_filter_eq
    by auto

  have filter_simp: "(\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) = (\<lambda>x. (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> mem (args_ivl args) (nt - t)))"
    by auto
  have filter_simp': "((\<lambda>(t, _). memR (args_ivl args) (nt - t)) \<circ> (\<lambda>(t, l, r). (t, r))) = (\<lambda>(t, _). memR (args_ivl args) (nt - t))"
    by auto
  have filter_simp'': "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t, _). mem (args_ivl args) (mt - t) \<and> memR (args_ivl args) (nt - t))"
    by auto

  from assms(1) have auxlist_eqs:
    "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
    "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
    unfolding valid_nmtaux_def prod.case by blast+
  then have auxlist_concat: "filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist @ filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist = auxlist"
    unfolding auxlist_data_prev_def auxlist_data_in_def
    by auto

  have "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using lin_data_in''_eq
    by auto
  moreover have in_eqs:
      "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
      "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    using assms(1)
    unfolding valid_nmtaux_def prod.case by blast+
  ultimately have "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist)) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist))"
    unfolding auxlist_data_in_def auxlist_data_prev_def
    by auto
  then have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist)) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist))"
    using filter_map[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, l, r). (t, r))" "(filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist)"]
    by (auto simp add: filter_simp')
  then have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) ((filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist)) @ (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    by auto
  then have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) ((filter (\<lambda>(t, _). mem (args_ivl args) (mt - t) \<and> memR (args_ivl args) (nt - t)) auxlist) @ (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). mem (args_ivl args) (mt - t))" auxlist]
    by (auto simp add: filter_simp'')
  then have x: "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) ((filter (\<lambda>(t, _). mem (args_ivl args) (mt - t) \<and> mem (args_ivl args) (nt - t)) auxlist) @ (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    using mem_mt_and_memR_imp_mem[of mt nt args] nt_mono time
    by auto
  moreover have filter_simp': "(\<lambda>(t, _). mem (args_ivl args) (mt - t) \<and> mem (args_ivl args) (nt - t)) = (\<lambda>x. (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (nt - t)))"
    by auto
  ultimately have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) ((filter (\<lambda>x. (case x of (t, _) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, _) \<Rightarrow> mem (args_ivl args) (nt - t))) auxlist) @ (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    by (simp only: filter_simp')
  moreover have filter_simp': "filter (\<lambda>x. (case x of (t, _) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, _) \<Rightarrow> mem (args_ivl args) (nt - t))) auxlist = filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist)"
    using filter_filter[of "(\<lambda>(t, _). mem (args_ivl args) (nt - t))" "(\<lambda>(t, _). mem (args_ivl args) (mt - t))" auxlist]
    by auto
  ultimately have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist) @ filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist))"
    unfolding filter_simp'
    by auto
  then have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) ((filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist) @ (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    by auto
  then have "map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) auxlist) = linearize data_in''"
    using auxlist_concat
    by auto
  moreover have "\<forall>t. (memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) = (mem (args_ivl args) (nt - t))"
    by blast
  ultimately have "map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) auxlist) = linearize data_in''"
    by auto
  then have lin_data_in''_eq: "map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) = linearize data_in''"
    using filter_filter[of "(\<lambda>(t, _). mem (args_ivl args) (nt - t))" "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" auxlist]
    by (auto simp add: filter_simp)
  then show auxlist_data_in: "map (\<lambda>(t, l, r). (t, r)) (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) = linearize data_in''"
    unfolding auxlist_data_in_def
    by auto

  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (nt - t))) = (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t))"
    by auto
  have filter_simp': "(\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) = (\<lambda>(t, _). mem (args_ivl args) (nt - t))"
    by auto


  from assms(1) have "auxlist_data_prev args mt auxlist = (linearize data_prev)"
                     "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
    unfolding valid_nmtaux_def prod.case by blast+
  then have prev_drop_eq: "(linearize data_prev) = drop (length (linearize data_in)) auxlist" by auto

  have "length (linearize data_in'') + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using data_in''_len
    by auto
  then have "length (linearize data_in'') = length (linearize data_in) - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto

  
  have memR: "\<forall>db \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist). memR (args_ivl args) (nt - time db)"
    unfolding time_def
    by auto
  have "sorted (map fst auxlist)" using assms(1) unfolding valid_nmtaux_def prod.case by blast
  then have sorted: "sorted (map fst (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist))"
    using sorted_filter
    by blast
  have "length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) = length (linearize data_in'')"
    by (simp flip: lin_data_in''_eq)

  then have filter_take_eq: "filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using take_filter_mem[OF memR sorted]
    by auto
  then show auxlist_data_in_take_eq: "auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    unfolding auxlist_data_in_def
    by auto

  from filter_take_eq have "(filter (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using filter_filter[of "(\<lambda>(t, _). mem (args_ivl args) (nt - t))" "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" auxlist]
    by (auto simp add: filter_simp)
  then have filter_auxlist_take: "(filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    by (simp only: filter_simp')

  have filter_simp: "(\<lambda>(t, _). mem (args_ivl args) (nt - t)) = (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> memL (args_ivl args) (nt - t))"
    by auto
  have filter_simp': "(\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> memL (args_ivl args) (nt - t)) = (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)))"
    by auto
  have filter_simp'': "(\<lambda>x. \<not> (case x of (t, _) \<Rightarrow> memL (args_ivl args) (nt - t))) = (\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t))"
    by auto

  have "(filter (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> memL (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using filter_auxlist_take
    by (auto simp add: filter_simp)
  then have "filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using filter_filter[of "(\<lambda>(t, _). mem (args_ivl args) (nt - t))" "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" auxlist]
    by (auto simp add: filter_simp')
  then have "filter (\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = drop (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using filter_take_drop[of "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)" "(length (linearize data_in''))"]
    by (simp only: filter_simp'')
  then show "auxlist_data_prev args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) =
    drop (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    unfolding auxlist_data_prev_def
    by auto

  {
    fix as

    define idx_oldest_mv where "idx_oldest_mv = (\<lambda>move::(ts \<times> 'a list set \<times> 'a list set) list.
      idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + length move - length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move)
    )"
    define idx_mid_mv where "idx_mid_mv = (\<lambda>move::(ts \<times> 'a list set \<times> 'a list set) list.
      idx_mid + length move
    )"
    define lin_data_in''_mv where "lin_data_in''_mv = (\<lambda>move::(ts \<times> 'a list set \<times> 'a list set) list.
      linearize data_in' @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move)
    )"

    have filter_simp: "(\<lambda>x. \<not> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))"
      by auto

    have data_in'_eq: "linearize data_in' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)"
      unfolding data_in'_def
      using takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
            dropWhile_queue_rep[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
            data_sorted[OF assms(1)] sorted_filter_dropWhile_memR[of "linearize data_in" args nt]
      by auto

    {
      fix move::"(ts \<times> 'a list set \<times> 'a list set) list"
      have "length ((linearize data_in)) + idx_oldest = idx_mid"
        using data_in_len
        by blast
      then have "length (lin_data_in''_mv move) + idx_oldest_mv move = idx_mid_mv move"
        unfolding lin_data_in''_mv_def idx_oldest_mv_def idx_mid_mv_def
        unfolding data_in'_eq
        using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "move"]
              sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "linearize data_in"]
        by (auto simp add: filter_simp)
    }
    then have mv_ln_eq: "\<forall>move. length (lin_data_in''_mv move) + idx_oldest_mv move = idx_mid_mv move" 
      by auto

    define tuple_since_hist_mv where "tuple_since_hist_mv = (\<lambda>(move::(ts \<times> 'a list set \<times> 'a list set) list) tuple.
      if ((idx_mid_mv move) = (idx_oldest_mv move)) then
        Mapping.empty
      else
        fst (fold fold_op_f move tuple)
    )"
   
    define hist_sat_mv where "hist_sat_mv = (\<lambda>move tuple.
      (case (lin_data_in''_mv move)
        of [] \<Rightarrow>
          {} 
        | (db#dbs) \<Rightarrow>
          ((fst o snd) (fold fold_op_f move tuple)) \<union> {as \<in> (snd db).
            case (Mapping.lookup (tuple_since_hist_mv move tuple) as) of
              Some idx \<Rightarrow> idx \<le> (idx_oldest_mv move)
            | None \<Rightarrow> False
          })
    )"

    define since_sat_mv where "since_sat_mv = (\<lambda>move tuple.
      if ((idx_mid_mv move) = (idx_oldest_mv move)) then
        {}
      else
        (snd o snd o snd) (fold fold_op_f move tuple)
    )"

    define data_in'_aux where "data_in'_aux =
      filter (\<lambda>(t, _). memR (args_ivl args) (nt - t))(take (length (linearize data_in)) auxlist)
    "

    have filter_map_simp: "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) = filter ((\<lambda>(t, _). memR (args_ivl args) (nt - t)) \<circ> (\<lambda>(t, l, r). (t, r)))"
      by (metis (mono_tags, lifting) case_prod_beta' fst_conv o_apply)

    have data_in'_aux_eq: "map (\<lambda>(t, l, r). (t, r)) data_in'_aux = linearize data_in'"
      using in_eqs(1) auxlist_eqs(2)
      unfolding data_in'_aux_def data_in'_eq
      using filter_map[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, l, r). (t, r))" "(take (length (linearize data_in)) auxlist)"]
      by (auto simp add: filter_map_simp)

    define lin_data_in''_aux_mv where "lin_data_in''_aux_mv = (\<lambda>move::(ts \<times> 'a list set \<times> 'a list set) list.
      data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move
    )"

    have data_in''_aux_eq: "\<forall>move. map (\<lambda>(t, l, r). (t, r)) (lin_data_in''_aux_mv move) = lin_data_in''_mv move"
      using data_in'_aux_eq
      unfolding lin_data_in''_aux_mv_def lin_data_in''_mv_def
      by auto

    define init_tuple where "init_tuple = (tuple_since_hist, hist_sat, idx_mid, since_sat)"

    define get_idx_move::"(('a list, nat) mapping \<times> 'a list set \<times> nat \<times> 'a list set) \<Rightarrow> nat"
      where "get_idx_move = fst o snd o snd"

    from assms(1) have tuple_init_props: "(\<forall>as. (case Mapping.lookup tuple_since_hist as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx)
    )"
      unfolding valid_nmtaux_def prod.case by blast (* map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)*)


    from assms(1) have in_eq: "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
      unfolding valid_nmtaux_def prod.case by blast
    {
      fix P
      have "(\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). P r) = (\<forall>(t, r) \<in> set (linearize data_in). P r)"
      proof (rule iffI)
        assume "(\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). P r)"
        then have "\<forall>(t, r)\<in>set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)). P r"
          by auto
        then show "(\<forall>(t, r) \<in> set (linearize data_in). P r)" using in_eq by auto
      next
        assume "\<forall>(t, r)\<in>set (linearize data_in). P r"
        then have "\<forall>(t, r)\<in>set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)). P r"
          using in_eq
          by auto
        then show "\<forall>(t, l, r)\<in>set (auxlist_data_in args mt auxlist). P r" by auto
      qed
    }
    then have "\<forall>P. (\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). P r) = (\<forall>(t, r) \<in> set (linearize data_in). P r)"
      by auto
    moreover from assms(1) have "(\<forall>tuple. tuple \<in> hist_sat \<longleftrightarrow>
        (\<not>Queue.is_empty data_in) \<and> (
          \<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r
      ))"
      unfolding valid_nmtaux_def prod.case by blast
    ultimately have tuple_init_props_hist_sat: "(\<forall>tuple. tuple \<in> hist_sat \<longleftrightarrow>
      (\<not>Queue.is_empty data_in) \<and> (
        \<forall>(t, r) \<in> set (linearize data_in). tuple \<in> r
    ))" by auto

    have tuple_init_props_since:
      "(\<forall>tuple. tuple \<in> since_sat \<longrightarrow>
        ((tuple \<in> hist_sat) \<or> tuple_since_lhs tuple (linearize data_in) args (auxlist_data_in args mt auxlist))
      )"
      "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in) args (auxlist_data_in args mt auxlist) \<longrightarrow>
        tuple \<in> since_sat
      )"
      using assms(1)
      unfolding valid_nmtaux_def prod.case by blast+

    
    have mv_data_in'': "linearize data_in'' = lin_data_in''_mv move"
      using data_in''_def fold_append_queue_map[of move' data_in'] move'_def
      unfolding lin_data_in''_mv_def
      by auto
    moreover have mv_idx_oldest': "idx_oldest' = idx_oldest_mv move"
      using idx_oldest'_eq
      unfolding idx_oldest_mv_def drop_prev_len_def move'_def
      by auto
    moreover have mv_idx_mid': "idx_mid' = idx_mid_mv move"
      unfolding idx_mid_mv_def idx_mid'_def init_tuple_def
      by auto
    ultimately have "length (lin_data_in''_mv move) + (idx_oldest_mv move) = (idx_mid_mv move)"
      using data_in''_len'
      by auto
    moreover have "sorted (map fst move)"
      unfolding move_filter
      using data_sorted(1)[OF assms(1)]
      by (rule sorted_filter)
    moreover have "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set move. t < t'"
      unfolding move_filter
      using data_sorted(3)[OF assms(1)]
      by fastforce
    moreover have "\<forall>(t, l, r) \<in> set move. table (args_L args) l \<and> table (args_R args) r"
    proof -
      have
        "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_L args) as)"
        "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_R args) as)"
        using assms(1)
        by (auto simp only: valid_nmtaux_def)
      then show ?thesis
        unfolding move_filter table_def relL_def relR_def
        by auto
    qed
    ultimately have "
    \<comment> \<open>historically\<close>
    (case Mapping.lookup (tuple_since_hist_mv move init_tuple) as of
      Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv move) (idx_oldest_mv move) (idx_mid_mv move) idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv move) (idx_oldest_mv move) (idx_mid_mv move) idx) \<and>
    (as \<in> (hist_sat_mv move init_tuple) \<longleftrightarrow>
      ((lin_data_in''_mv move) \<noteq> []) \<and> (
        \<forall>(t, r) \<in> set (lin_data_in''_mv move). as \<in> r
    )) \<and>
     \<comment> \<open>since\<close>
    (as \<in> (since_sat_mv move init_tuple) \<longrightarrow>        
      ((as \<in> (hist_sat_mv move init_tuple)) \<or> tuple_since_lhs as (lin_data_in''_mv move) args (lin_data_in''_aux_mv move))
    ) \<and>
    (tuple_since_lhs as (lin_data_in''_mv move) args (lin_data_in''_aux_mv move) \<longrightarrow>
      as \<in> (since_sat_mv move init_tuple)
    ) \<and>
    \<comment> \<open>other required properties\<close>
    get_idx_move (fold fold_op_f move init_tuple) = (idx_mid_mv move) \<and>
    (case Mapping.lookup (fst (fold fold_op_f move init_tuple)) as of Some idx \<Rightarrow> idx < (idx_mid_mv move) | None \<Rightarrow> True)"
    proof (induction move rule: rev_induct)
      case Nil
      then have lin_data_in''_eq: "lin_data_in''_mv [] = drop (length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))) (linearize data_in)"
        unfolding lin_data_in''_mv_def data_in'_def
        using takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
              dropWhile_queue_rep[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
              data_sorted[OF assms(1)] sorted_filter_dropWhile_memR[of "linearize data_in" args nt]
              drop_filter_memR[of "linearize data_in" "(args_ivl args)" nt ]
        by auto
      have idx_oldest'_eq: "idx_oldest_mv [] = idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
        unfolding idx_oldest_mv_def
        using Nil
        by auto

      have idx_mid'_eq: "idx_mid_mv [] = idx_mid"
        unfolding idx_mid_mv_def
        using Nil
        by (simp add: case_prod_beta')
      
      have tuple_since_hist'_eq: "fst (fold fold_op_f [] init_tuple) = fst init_tuple"
        using Nil
        by auto
      then have "case Mapping.lookup (tuple_since_hist_mv [] init_tuple) as of
        Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx
        | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx"
      proof (cases "(idx_mid_mv []) = (idx_oldest_mv [])")
        case True
        then have "tuple_since_hist_mv [] init_tuple = Mapping.empty"
          using True
          unfolding tuple_since_hist_mv_def
          by auto
        then have "Mapping.lookup (tuple_since_hist_mv [] init_tuple) as = None"
          by (simp add: Mapping.empty_def Mapping.lookup.abs_eq)
        moreover have "\<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx"
          using True Nil
          unfolding tuple_since_tp_def 
          by auto
        ultimately show ?thesis by auto
      next
        define idx_move where "idx_move = get_idx_move init_tuple"
        case non_empty: False
        have "case Mapping.lookup (fst (fold fold_op_f [] init_tuple)) as of
            None     \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx
          | Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx
        "
        proof (cases "Mapping.lookup (fst (fold fold_op_f [] init_tuple)) as")
          case None
          then have tuple_since_tp: "\<forall>idx. \<not>tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
            using tuple_since_hist'_eq Nil idx_mid'_eq tuple_init_props
            unfolding idx_move_def get_idx_move_def init_tuple_def
            by (auto simp add: option.case_eq_if)
          then have idx_props: "\<forall>idx<idx_mid. (
              linearize data_in = [] \<or>
              \<not>(\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
                as \<in> r
              ) \<or>
              \<not>(idx > idx_oldest \<longrightarrow> as \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))
            )"
            unfolding tuple_since_tp_def
            by blast
          {
            assume assm: "(linearize data_in) \<noteq> []"
            then have idx_props: "\<forall>idx<idx_mid. (
              \<not>(\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
                as \<in> r
              ) \<or>
              \<not>(idx > idx_oldest \<longrightarrow> as \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))
            )"
              using idx_props
              by blast

            then have "as \<notin> snd (last (linearize data_in))"
              using no_hist_last_not_sat[OF data_in_len tuple_since_tp assm]
              by auto
          }
          then have "(linearize data_in) \<noteq> [] \<longrightarrow> as \<notin> snd (last (linearize data_in))"
            by auto
          moreover have "(lin_data_in''_mv []) \<noteq> [] \<longrightarrow> (linearize data_in) \<noteq> [] \<and> (last (linearize data_in) = last (lin_data_in''_mv []))"
            using lin_data_in''_eq
            by auto
          ultimately have last_props: "lin_data_in''_mv [] \<noteq> [] \<longrightarrow> as \<notin> snd (last (lin_data_in''_mv []))"
            by auto
          {
            fix idx
            assume assm: "lin_data_in''_mv [] \<noteq> []" "idx < (idx_mid_mv [])" "(idx > (idx_oldest_mv []) \<longrightarrow> as \<notin> (snd ((lin_data_in''_mv [])!(idx-(idx_oldest_mv [])-1))))"
            then have "idx - (idx_oldest_mv []) < length (lin_data_in''_mv [])"
              using Nil
              by (metis diff_is_0_eq leI length_greater_0_conv less_diff_conv2 nat_less_le)
            then have "last (lin_data_in''_mv []) \<in> set (drop (idx-(idx_oldest_mv [])) (lin_data_in''_mv []))"
              by (metis drop_eq_Nil last_drop last_in_set leD)
            moreover have "as \<notin> snd (last (lin_data_in''_mv []))"
              using assm(1) last_props
              by auto
            ultimately have "\<exists>db \<in> set (drop (idx-(idx_oldest_mv [])) (lin_data_in''_mv [])). as \<notin> snd db"
              by auto
          }
          then have "\<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx"
            unfolding tuple_since_tp_def
            by (auto simp add: case_prod_beta')
          then show ?thesis using None by auto
        next
          case (Some idx)
          then have "Mapping.lookup tuple_since_hist as = Some idx"
            using tuple_since_hist'_eq
            unfolding init_tuple_def
            by simp
          then have "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
            using tuple_init_props[THEN spec[of _ as]]
            by simp
          then have idx_props: "(linearize data_in) \<noteq> []" "idx < idx_mid"
              "(\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
                as \<in> r
              )"
              "(idx > idx_oldest \<longrightarrow> as \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))"
            unfolding tuple_since_tp_def
            by auto
          then have idx_mid: "idx < (idx_mid_mv [])" using idx_mid'_eq by auto
          {
            define r where "r = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
            assume "\<exists>db \<in> set (drop (idx-(idx_oldest_mv [])) (lin_data_in''_mv [])). as \<notin> snd db"
            then obtain db where db_props: "db \<in> set (drop (idx - idx_oldest - r) (drop r (linearize data_in)))" "as \<notin> snd db"
              using idx_oldest'_eq lin_data_in''_eq
              unfolding r_def
              by auto
            then have  "db \<in> set (drop (idx - idx_oldest) (linearize data_in))"
              by (metis drop_list_shift in_set_dropD leI less_imp_le_nat)
            then have "False" using idx_props(3) db_props(2) by auto
          }
          then have "\<forall>(t, r) \<in> set (drop (idx-(idx_oldest_mv [])) (lin_data_in''_mv [])). as \<in> r"
            by fastforce
          moreover {
            define r where "r = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
            assume "idx > idx_oldest_mv []"
            then have idx_g: "idx > idx_oldest + r"
              using idx_oldest'_eq
              unfolding r_def
              by auto
            then have "(lin_data_in''_mv [])!(idx-(idx_oldest_mv [])-1) = linearize data_in!(idx-idx_oldest -1)"
              using idx_oldest'_eq lin_data_in''_eq
              unfolding r_def
              by (auto simp add: add.commute)
            moreover have "as \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1)))"
              using idx_props(4) idx_g
              by auto
            ultimately have "as \<notin> (snd ((lin_data_in''_mv [])!(idx-(idx_oldest_mv [])-1)))" by auto
          }
          ultimately have "tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx"
            using idx_mid non_empty Nil
            unfolding tuple_since_tp_def
            by auto
          then show ?thesis using Some by auto
        qed
        moreover have "tuple_since_hist_mv [] init_tuple = fst (fold fold_op_f [] init_tuple)"
          using non_empty
          unfolding tuple_since_hist_mv_def
          by auto
        ultimately show ?thesis by auto
      qed
      moreover have hist_sat_props: "(as \<in> (hist_sat_mv [] init_tuple) \<longleftrightarrow>
        ((lin_data_in''_mv []) \<noteq> []) \<and> (
          \<forall>(t, r) \<in> set (lin_data_in''_mv []). as \<in> r
        ))"
      proof -
        {
          assume assm: "as \<in> (hist_sat_mv [] init_tuple)"
          then have non_empty: "lin_data_in''_mv [] \<noteq> []"
            unfolding hist_sat_mv_def
            by auto
          then obtain db dbs where db_props: "lin_data_in''_mv [] = db # dbs"
            using list.exhaust
            by blast
          have "\<forall>(t, r) \<in> set (lin_data_in''_mv []). as \<in> r"
          proof -
            {
              fix t r
              assume "(t, r) \<in> set (lin_data_in''_mv [])"
              then have list_mem: "(t, r) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))"
                unfolding lin_data_in''_mv_def data_in'_eq
                by auto
              have "(fst \<circ> snd) (fold fold_op_f [] init_tuple) = hist_sat"
                unfolding init_tuple_def 
                by auto
              moreover have "tuple_since_hist_mv [] init_tuple = tuple_since_hist"
                using non_empty Nil(1)
                unfolding tuple_since_hist_mv_def init_tuple_def 
                by auto
              ultimately have "as \<in> hist_sat \<union> {as \<in> snd db. case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False}"
                using assm db_props
                unfolding hist_sat_mv_def
                by auto
              moreover {
                assume "as \<in> hist_sat"
                then have "\<forall>(t, r)\<in>set (linearize data_in). as \<in> r" using tuple_init_props_hist_sat by auto
                then have "as \<in> r" using list_mem by auto
              }
              moreover {
                assume "as \<in> {as \<in> snd db. case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False}"
                then have "as \<in> snd db" "(case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False)"
                  by auto
                then obtain idx where idx_props: "Mapping.lookup tuple_since_hist as = Some idx" "idx \<le> idx_oldest_mv []"
                  using case_optionE
                  by blast
                then have "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
                  using tuple_init_props
                  by (auto split: option.splits)
                then have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest) (linearize data_in)). as \<in> y)"
                  unfolding tuple_since_tp_def
                  by auto
                then have "(\<forall>(t, y)\<in>set (drop (idx_oldest_mv [] - idx_oldest) (linearize data_in)). as \<in> y)"
                  using idx_props(2)
                  by (meson diff_le_mono set_drop_subset_set_drop subsetD)
                then have "(\<forall>(t, y)\<in>set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)). as \<in> y)"
                  using data_sorted[OF assms(1)] drop_filter_memR[of "linearize data_in" "args_ivl args" nt]
                  unfolding idx_oldest_mv_def
                  by auto
                then have "as \<in> r" using list_mem by auto
              }
              ultimately have "as \<in> r" by auto
            }
            then show ?thesis by auto
          qed
          then have "((lin_data_in''_mv []) \<noteq> []) \<and> (
            \<forall>(t, r) \<in> set (lin_data_in''_mv []). as \<in> r
          )" using non_empty by auto
        }
        moreover {
          assume assm:
            "((lin_data_in''_mv []) \<noteq> [])" 
            "\<forall>(t, r) \<in> set (lin_data_in''_mv []). as \<in> r"
          then obtain db dbs where db_props: "lin_data_in''_mv [] = db # dbs"
            using list.exhaust
            by blast
          then have db_in: "db \<in> set (linearize data_in)"
            by (metis db_props in_set_dropD lin_data_in''_eq list.set_intros(1))
          have db_mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) db"
            using db_props
            unfolding lin_data_in''_mv_def data_in'_eq
            by (metis (no_types, lifting) append_Nil2 filter.simps(1) list.set_intros(1) list.simps(8) mem_Collect_eq set_filter)
          from assm(2) have all_relR: "\<forall>(t, r) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)). as \<in> r"
            unfolding lin_data_in''_mv_def data_in'_eq
            by auto

          have db_relR: "as \<in> snd db"
            using db_props assm(2)
            by auto

          have in_nonempty: "linearize data_in \<noteq> []" using assm(1) unfolding lin_data_in''_mv_def data_in'_eq by auto

          define l where "l = drop (length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))) (linearize data_in)"
          define in_but_last where "in_but_last = (take (length (linearize data_in) - 1) (linearize data_in))"

          have l_props: "l \<noteq> []"
               "\<forall>(t, r)\<in>set l. as \<in> r"
            using assm data_sorted[OF assms(1)] drop_filter_memR[of "linearize data_in" "args_ivl args" nt]
            unfolding lin_data_in''_mv_def data_in'_eq l_def
            by auto
          then have last_l_mem: "last (linearize data_in) \<in> set l"
            unfolding l_def
            by (metis drop_eq_Nil last_drop last_in_set leI)
          then have last_relR: "as \<in> snd (last (linearize data_in))"
            using l_props(2)
            by auto
          have data_in_split: "linearize data_in = in_but_last @ [last (linearize data_in)]"
            using in_nonempty
                  drop_last[of "linearize data_in"]
            unfolding in_but_last_def
            by (metis append_butlast_last_id butlast_conv_take)

          {
            assume assm_all: "\<forall>(t, r) \<in> set in_but_last. as \<in> r"
            then have "\<forall>(t, r) \<in> set (linearize data_in). as \<in> r"
              using assm_all l_props(2) data_in_split last_l_mem
              by (metis in_set_simps(4) list_appendE set_ConsD)
            then have "as \<in> hist_sat" using tuple_init_props_hist_sat in_nonempty Queue.is_empty_alt
              by auto
          }
          moreover {
            define A where "A = {i \<in> {0..<length (linearize data_in) - 1}. as \<notin> snd ((linearize data_in)!i)}"
            define j where "j = Max A"
            assume "\<exists>(t, r) \<in> set in_but_last. as \<notin> r"
            then obtain i where "i \<in> {0..<length (linearize data_in) - 1}" "as \<notin> snd ((linearize data_in)!i)"
              unfolding in_but_last_def
              by (metis (no_types, lifting) case_prodE diff_le_self imageE nth_image snd_conv)
            then have "i \<in> A" unfolding A_def by auto
            then have A_props: "A \<noteq> {}" "finite A" unfolding A_def by auto
            then have "j \<in> A" unfolding j_def by auto
            then have j_props: "j \<in> {0..<length (linearize data_in) - 1}" "as \<notin> snd ((linearize data_in)!j)"
              unfolding A_def
              by auto
            then have j_l: "(idx_oldest + j + 1) < idx_mid"
              using data_in_len
              by auto
            {
              assume "j + 1 > length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
              then have j_geq: "j \<ge> length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
                by auto
              moreover have "filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in) = takeWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)"
                using data_sorted[OF assms(1)] sorted_filter_takeWhile_not_memR[of "linearize data_in" args nt]
                by auto
              moreover have "linearize data_in = (takeWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) @ (dropWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
                by auto
              ultimately have "((linearize data_in)!j) = (dropWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))!(j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)))"
                using j_props(1) idx_append_snd[of j "(takeWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))" "linearize data_in" "(dropWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"]
                by auto
              then have jth: "((linearize data_in)!j) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)!(j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)))"
                using data_sorted[OF assms(1)] sorted_filter_dropWhile_memR[of "linearize data_in" args nt]
                by auto
              have "j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) \<in> {0..<length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))}"
                using j_geq j_props(1) sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(linearize data_in)"]
                by (auto simp add: filter_simp)
              then have "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)!(j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))"
                using nth_set_member[of "j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))" "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)"]
                by auto
              then have "as \<in> snd ((linearize data_in)!j)"
                using jth all_relR
                by auto
              then have "False" using j_props(2) by auto
            }
            then have j_suc_leq: "j + 1 \<le> length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
              using not_le_imp_less
              by blast
            {
              fix t y
              assume "(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) (linearize data_in))"
              then have assm: "(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) (in_but_last @ [last (linearize data_in)]))"
                using data_in_split
                by auto
              have "as \<in> y"
              proof (cases "(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) in_but_last)")
                case True
                then have "(t, y) \<in> set (drop (j + 1) in_but_last)"
                  by simp
                then obtain k' where "k' < length (drop (j + 1) in_but_last)" "(drop (j+1) in_but_last)!k' = (t, y)"
                  unfolding in_set_conv_nth by blast
                then have k'_props: "k' \<in> {0..<length in_but_last - j - 1}" "(drop (j+1) in_but_last)!k' = (t, y)"
                  by simp_all
                
                define k where "k = k' + j + 1"
                have "in_but_last!k = (t, y)" "k \<in> {j+1..<length in_but_last}"
                  using k'_props j_props(1)
                  unfolding k_def
                  by (auto simp add: add.commute)
                then have k_props: "(linearize data_in)!k = (t, y)" "k \<in> {j+1..<length (linearize data_in) - 1}"
                  unfolding in_but_last_def
                  by auto
                {
                  assume "as \<notin> y"
                  then have "k \<in> A" using k_props unfolding A_def by auto
                  then have "k \<le> j" using A_props unfolding j_def by auto
                  then have "False" using k_props(2) by auto
                }
                then show ?thesis by auto
              next
                case False
                {
                  assume "(t, y) \<noteq> last (linearize data_in)"
                  then have "(t, y) \<notin> set (drop ((idx_oldest + j + 1) - idx_oldest) (in_but_last @ [last (linearize data_in)]))"
                    using False
                    using in_set_dropD
                    by fastforce
                  then have "False"
                    using assm
                    by auto
                }
                then have "(t, y) = last (linearize data_in)" using assm by auto
                then show ?thesis
                  using last_relR
                  by (metis snd_conv)
              qed
            }
            then have all_relR: "(\<forall>(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) (linearize data_in)). as \<in> y)"
              by auto

            moreover have "as \<notin> snd (linearize data_in ! ((idx_oldest + j + 1) - idx_oldest - 1))"
              using j_props(2)
              by auto

            ultimately have tp: "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid (idx_oldest + j + 1)"
              using in_nonempty j_l
              unfolding tuple_since_tp_def
              by auto
            then obtain idx where idx_props:
              "Mapping.lookup tuple_since_hist as = Some idx"
              "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
              using tuple_init_props
              by (auto split: option.splits)
            then have "idx = (idx_oldest + j + 1)"
              using tuple_since_hist_lookup_eq[OF tuple_init_props tp _ data_in_len]
              by auto                              
            moreover have "idx_oldest + j + 1 \<le> idx_oldest_mv []"
              using j_suc_leq
              unfolding idx_oldest_mv_def
              by auto
            ultimately have "as \<in> {as \<in> snd db. case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False}"
              using db_relR idx_props(1)
              unfolding idx_oldest_mv_def
              by auto
          }

          ultimately have "as \<in> hist_sat \<union> {as \<in> snd db. case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False}"
            by auto
          then have "as \<in> (hist_sat_mv [] init_tuple)"
            using assm(1) db_props Nil(1)
            unfolding hist_sat_mv_def init_tuple_def tuple_since_hist_mv_def
            by (auto split: list.splits)
        }
        ultimately show ?thesis
          by blast
      qed
      moreover have "(as \<in> (since_sat_mv [] init_tuple) \<longrightarrow>
        ((as \<in> (hist_sat_mv [] init_tuple)) \<or> tuple_since_lhs as (lin_data_in''_mv []) args (lin_data_in''_aux_mv []))
      )"
      proof -
        {
          assume "as \<in> (since_sat_mv [] init_tuple)"
          then have since_mem: "idx_mid_mv [] \<noteq> idx_oldest_mv []"
                    "as \<in> since_sat"
            unfolding since_sat_mv_def init_tuple_def
            by (auto split: if_splits)
          then have non_empty: "lin_data_in''_mv [] \<noteq> []"
            using mv_ln_eq
            by (metis add_cancel_left_left list.size(3))

          from assms(1) have in_eq: "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
            unfolding valid_nmtaux_def prod.case by blast

          from assms(1) have auxlist_props: "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db))"
            unfolding valid_nmtaux_def prod.case by blast
          then have in_memR: "\<forall>db\<in>set (auxlist_data_in args mt auxlist). memR (args_ivl args) (mt - time db)"
            unfolding auxlist_data_in_def
            by auto

          have "as \<in> hist_sat \<or> tuple_since_lhs as (linearize data_in) args (auxlist_data_in args mt auxlist)"
            using since_mem tuple_init_props_since(1)
            by auto
          moreover {
            assume "as \<in> hist_sat"
            then have "\<forall>(t, r)\<in>set (linearize data_in). as \<in> r"
              using tuple_init_props_hist_sat
              by auto
            then have "\<forall>(t, r)\<in>set (lin_data_in''_mv []). as \<in> r"
              unfolding lin_data_in''_mv_def data_in'_eq
              by auto
            then have "as \<in> (hist_sat_mv [] init_tuple)"
              using non_empty hist_sat_props
              by auto
          }
          moreover {
            assume "tuple_since_lhs as (linearize data_in) args (auxlist_data_in args mt auxlist)"
            then obtain n where n_props:
              "n\<in>{0..<length (linearize data_in)}"
              "let suffix = drop n (auxlist_data_in args mt auxlist) in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) as)"
              "linearize data_in \<noteq> []"
              unfolding tuple_since_lhs_def
              by auto
            then have n_l: "n < length (auxlist_data_in args mt auxlist)"
              using auxlist_eqs(2)
              by (metis atLeastLessThan_iff in_eq length_map)
            define suffix where "suffix = drop n (auxlist_data_in args mt auxlist)"
            
            have sorted_auxlist: "sorted (map fst auxlist)" using assms(1) unfolding valid_nmtaux_def prod.case by blast
            then have sorted_in: "sorted (map fst (auxlist_data_in args mt auxlist))"
              unfolding suffix_def auxlist_data_in_def
              by (metis (no_types, lifting) sorted_filter)


            then have suffix_props:
              "(\<forall>(t, l, y)\<in>set suffix. as \<in> y)"
              "join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) as)"
              "suffix \<noteq> []"
              using n_props n_l
              unfolding suffix_def
              by (auto simp add: Let_def)

            moreover have hd_suffix: "hd suffix = (auxlist_data_in args mt auxlist)!n"
              using suffix_props(3)
              unfolding suffix_def
              by (simp add: hd_drop_conv_nth)

            ultimately have relL: "join_cond (args_pos args) (relL ((auxlist_data_in args mt auxlist)!n)) (restrict (args_L args) (args_R args) as)"
              by auto

            {
              define l where "l = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist))"
              assume assm: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist)!n)"
              have "lin_data_in''_aux_mv [] = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)"
                using auxlist_eqs(2)
                unfolding lin_data_in''_aux_mv_def data_in'_aux_def
                by auto
              then have lin_data_in''_eq: "lin_data_in''_aux_mv [] = drop l (auxlist_data_in args mt auxlist)"
                using drop_filter_memR[OF sorted_in, of "args_ivl args" nt]
                unfolding l_def
                by auto

              define n' where "n' = n - l"
              {
                assume "l > n"
                then have "((auxlist_data_in args mt auxlist)!n) \<in> set (take l (auxlist_data_in args mt auxlist))"
                  using n_l n_props(1) 
                  by (metis atLeastLessThan_iff image_eqI nat_le_linear nth_image take_all)
                then have "((auxlist_data_in args mt auxlist)!n) \<in> set (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist))"
                  using take_filter_not_memR[OF sorted_in, of "args_ivl args" nt]
                  unfolding l_def
                  by auto
                then have "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist)!n)"
                  by auto
                then have "False"
                  using assm
                  by auto
              }
              then have l_leq: "l \<le> n" using not_le_imp_less by blast
              then have "\<forall>(t, l, r)\<in>set (drop (n-l) (drop l (auxlist_data_in args mt auxlist))). as \<in> r"
                using suffix_props(1) n_l
                unfolding suffix_def
                by auto
              then have "\<forall>(t, l, r)\<in>set (drop (n-l) (lin_data_in''_aux_mv [])). as \<in> r"
                using lin_data_in''_eq
                by auto
              moreover have "join_cond (args_pos args) (relL (hd (drop (n-l) (lin_data_in''_aux_mv [])))) (restrict (args_L args) (args_R args) as)"
                using lin_data_in''_eq l_leq suffix_props(2)
                unfolding suffix_def
                by auto
              ultimately have "(
                let suffix = drop n' (lin_data_in''_aux_mv [])
                in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) as))"
                by (simp only: Let_def n'_def)
              moreover have "n'\<in>{0..<length (lin_data_in''_mv [])}"
                unfolding n'_def
                using n_l lin_data_in''_eq l_leq data_in''_aux_eq
                by (metis (mono_tags) atLeastLessThan_iff diff_less_mono length_drop length_map zero_le)
              ultimately have "tuple_since_lhs as (lin_data_in''_mv []) args (lin_data_in''_aux_mv [])"
                using non_empty
                unfolding tuple_since_lhs_def
                by blast
            }
            moreover {
              assume assm: "\<not>(\<lambda>(t, _). memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist)!n)"
              {
                fix t r
                assume "(t, r) \<in> set (lin_data_in''_mv [])"
                then have data_in_mem: "(t, r) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))"
                  unfolding lin_data_in''_mv_def data_in'_eq
                  by auto
                then have memR: "memR (args_ivl args) (nt - t)" by auto

                have filter_simp: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) = ((\<lambda>(t, _). memR (args_ivl args) (nt - t)) \<circ> (\<lambda>(t, l, r). (t, r)))"
                  by auto

                have "map (\<lambda> (t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)"
                  using in_eq filter_map[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda> (t, l, r). (t, r))" "(auxlist_data_in args mt auxlist)"]
                  by (auto simp add: filter_simp)
                then have "(t, r) \<in> set (map (\<lambda> (t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)))"
                  using data_in_mem
                  by auto
                then obtain l where tlr_mem: "(t, l, r) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist))"
                  by auto
                then have mem: "mem (args_ivl args) (mt - t)"
                  using nt_mono(1) time
                  unfolding auxlist_data_in_def
                  by auto
                then have "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
                  using tlr_mem
                  unfolding auxlist_data_in_def
                  by auto
                then obtain i where i_props:
                  "i \<in> {0..<length(auxlist_data_in args mt auxlist)}"
                  "(auxlist_data_in args mt auxlist)!i = (t, l, r)"
                  by (meson atLeastLessThan_iff nth_the_index the_index_bounded zero_le)
                {
                  assume "i \<le> n"
                  then have "(map fst (auxlist_data_in args mt auxlist))!i \<le> (map fst (auxlist_data_in args mt auxlist))!n"
                    by (rule sorted_nth_mono[OF sorted_in]) (simp add: n_l)
                  then have "t \<le> fst ((auxlist_data_in args mt auxlist)!n)"
                    using i_props n_l
                    by simp
                  then have "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist)!n)"
                    using memR memR_antimono[of "args_ivl args"]
                    by auto
                  then have "False" using assm by blast
                }
                then have "i > n" using not_le_imp_less by blast
                then have "(t, l, r) \<in> set suffix"
                  using i_props
                  unfolding suffix_def in_set_conv_nth
                  by (auto intro!: exI[of _ "i - n"])
                then have "as \<in> r" using suffix_props by auto
              }
              then have "\<forall>(t, r)\<in>set (lin_data_in''_mv []). as \<in> r" by auto
              then have "as \<in> (hist_sat_mv [] init_tuple)"
                using non_empty hist_sat_props
                by auto
            }

            ultimately have "((as \<in> (hist_sat_mv [] init_tuple)) \<or> tuple_since_lhs as (lin_data_in''_mv []) args (lin_data_in''_aux_mv []))"
              by fast
          }
          ultimately have "((as \<in> (hist_sat_mv [] init_tuple)) \<or> tuple_since_lhs as (lin_data_in''_mv []) args (lin_data_in''_aux_mv []))"
            by blast
        }
        then show ?thesis by auto
      qed
      moreover have "(tuple_since_lhs as (lin_data_in''_mv []) args (lin_data_in''_aux_mv []) \<longrightarrow>
        as \<in> (since_sat_mv [] init_tuple)
      )"
      proof -
        {
          assume assm: "tuple_since_lhs as (lin_data_in''_mv []) args (lin_data_in''_aux_mv [])"
          then have non_empty: "lin_data_in''_mv [] \<noteq> []"
            unfolding tuple_since_lhs_def
            by auto
          
          have sorted_auxlist: "sorted (map fst auxlist)" using assms(1) unfolding valid_nmtaux_def prod.case by blast
          then have sorted_in: "sorted (map fst (auxlist_data_in args mt auxlist))"
            unfolding auxlist_data_in_def
            by (metis (no_types, lifting) sorted_filter)

          define l where "l = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist))"

          have "lin_data_in''_aux_mv [] = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)"
            using auxlist_eqs(2)
            unfolding lin_data_in''_aux_mv_def data_in'_aux_def
            by auto
          then have lin_data_in''_eq: "lin_data_in''_aux_mv [] = drop l (auxlist_data_in args mt auxlist)"
            using drop_filter_memR[OF sorted_in, of "args_ivl args" nt]
            unfolding l_def
            by auto

          moreover obtain n where n_props:
            "n\<in>{0..<length (lin_data_in''_mv [])}"
            "let suffix = drop n (lin_data_in''_aux_mv []) in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) as)"
            using assm
            unfolding tuple_since_lhs_def
            by auto

          ultimately have "let suffix = drop (l+n) (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and>
            join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) as)
          )"
            by (simp add: add.commute)

          moreover have "l + n < length (linearize data_in)"
          proof -
            have "n < length (lin_data_in''_mv [])"
              using n_props(1) by simp
            also have "length (lin_data_in''_mv []) = length (auxlist_data_in args mt auxlist) - l"
              using lin_data_in''_eq by (simp flip: data_in''_aux_eq)
            also have "\<dots> = length (linearize data_in) - l"
              by (simp flip: in_eq)
            finally show ?thesis
              by linarith
          qed

          ultimately have "tuple_since_lhs as (linearize data_in) args (auxlist_data_in args mt auxlist)"
            using non_empty
            unfolding tuple_since_lhs_def
            by fastforce
          then have "as \<in> since_sat"
            using tuple_init_props_since(2)
            by auto
          then have "as \<in> (since_sat_mv [] init_tuple)"
            using mv_ln_eq non_empty
            unfolding since_sat_mv_def init_tuple_def
            by (metis List.fold_simps(1) add_cancel_left_left comp_apply length_0_conv snd_conv)
        }
        then show ?thesis by auto
      qed
      moreover have "get_idx_move (fold fold_op_f [] init_tuple) = idx_mid_mv []"
        unfolding get_idx_move_def init_tuple_def idx_mid_mv_def
        by auto
      moreover have "(case Mapping.lookup (fst (fold fold_op_f [] init_tuple)) as of Some idx \<Rightarrow> idx < idx_mid_mv [] | None \<Rightarrow> True)"
      proof -
        have "fst (fold fold_op_f [] init_tuple) = tuple_since_hist" unfolding init_tuple_def by auto
        moreover have "idx_mid_mv [] = idx_mid" unfolding idx_mid_mv_def by auto
        moreover have "(case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx < idx_mid | None \<Rightarrow> True)"
          using tuple_init_props
          unfolding tuple_since_tp_def
          by (auto split: option.splits)
        ultimately show ?thesis by auto
      qed
      ultimately show ?case by auto
    next
      case (snoc x xs)
      have assm:
        "length (lin_data_in''_mv (xs @ [x])) + idx_oldest_mv (xs @ [x]) = idx_mid_mv (xs @ [x])"
        using snoc
        by auto
      define r where "r = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (xs @ [x]))"
      have r_leq: "r \<le> length (xs @ [x])"
        unfolding r_def
        using length_filter_le[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(xs @ [x])"]
        by auto
      define r' where "r' = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs)"
      have r'_leq: "r' \<le> length xs"
        unfolding r'_def
        using length_filter_le[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "xs"]
        by auto


      have "length (linearize data_in') + idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + length xs = idx_mid_mv xs"
        using assm(1) r_leq snoc(2)
        unfolding lin_data_in''_mv_def idx_mid_mv_def idx_oldest_mv_def r_def
        by (auto simp add: case_prod_beta')
      then have "length (linearize data_in') + r' + (idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + length xs - r') = idx_mid_mv xs"
        using r'_leq
        unfolding idx_mid_mv_def
        by auto
      
      then have "length (lin_data_in''_mv xs) + idx_oldest_mv xs = idx_mid_mv xs"
        using snoc(2)
        unfolding r'_def idx_oldest_mv_def lin_data_in''_mv_def
        by auto
      moreover have xs_sorted: "sorted (map fst xs)"
        using snoc(3)
        by (simp add: sorted_append)
      moreover have xs_ts: "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set xs. t < t'"
        using snoc(4)
        by auto
      moreover have "\<forall>(t, l, r) \<in> set xs. table (args_L args) l \<and> table (args_R args) r"
        using snoc(5)
        by auto
      ultimately have IH: "case Mapping.lookup (tuple_since_hist_mv xs init_tuple) as of
          None   \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx
        | Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
        "get_idx_move (fold fold_op_f xs init_tuple) = idx_mid_mv xs"
        "(case Mapping.lookup (fst (fold fold_op_f xs init_tuple)) as of None \<Rightarrow> True | Some idx \<Rightarrow> idx < idx_mid_mv xs)"
        "as \<in> (hist_sat_mv xs init_tuple) \<longleftrightarrow>
          ((lin_data_in''_mv xs) \<noteq> []) \<and> (
            \<forall>(t, r) \<in> set (lin_data_in''_mv xs). as \<in> r
        )"
        "(as \<in> since_sat_mv xs init_tuple \<longrightarrow> as \<in> hist_sat_mv xs init_tuple \<or> tuple_since_lhs as (lin_data_in''_mv xs) args (lin_data_in''_aux_mv xs))"
        "(tuple_since_lhs as (lin_data_in''_mv xs) args (lin_data_in''_aux_mv xs) \<longrightarrow> as \<in> since_sat_mv xs init_tuple)"
        using snoc(1)
        by auto

      define tuple where "tuple = (fold fold_op_f xs init_tuple)"
      define tuple_since_hist' where "tuple_since_hist' = fst tuple"
      define joined_mapping where "joined_mapping = Mapping.filter (\<lambda>as _. as \<in> (relR x)) tuple_since_hist'"

      have fold_IH_since_hist: "fst (fold_op_f x tuple) = upd_set joined_mapping (\<lambda>_. (get_idx_move tuple)) ((relR x) - Mapping.keys joined_mapping)"
        unfolding fold_op_f_def relR_def relL_def joined_mapping_def get_idx_move_def tuple_since_hist'_def
        by (auto simp add: Let_def case_prod_beta')

      define hist_sat' where "hist_sat' = (fst o snd) tuple"
      have fold_IH_hist_sat: "(fst o snd) (fold_op_f x tuple) = hist_sat' \<inter> (relR x)"
        unfolding fold_op_f_def relR_def hist_sat'_def
        by (auto simp add: Let_def case_prod_beta')

      have x_table:
        "table (args_L args) (relL x)"
        "table (args_R args) (relR x)"
        using snoc(5)
        unfolding relL_def relR_def
        by (auto)

      define since_sat' where "since_sat' = (snd o snd o snd) tuple"
      have fold_IH_since_sat: "(snd o snd o snd) (fold_op_f x tuple) = (since_sat' \<inter> (relR x)) \<union> proj_tuple_in_join_optim (args_pos args) (relR x) (args_R args) (relL x) (args_L args)"
        unfolding fold_op_f_def relR_def relL_def since_sat'_def
        by (auto simp add: Let_def case_prod_beta')
      then have fold_IH_since_sat: "(snd o snd o snd) (fold_op_f x tuple) = (since_sat' \<inter> (relR x)) \<union> {as \<in> (relR x). proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as (relL x)}"
        using proj_tuple_in_join_optim_equiv[OF x_table(2) valid_nmtaux_distinct(2)[OF assms(1)], of "args_pos args"]
        by blast

      {
        assume non_empty: "lin_data_in''_mv (xs @ [x]) \<noteq> []"
        assume mem: "\<not> (\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
        {
          fix db
          assume "db \<in> set xs"
          then have "fst db \<le> fst x"
            using snoc(3)
            by (simp add: sorted_append)
          then have  "\<not> (\<lambda>(t, _). memR (args_ivl args) (nt - t)) db"
            using mem memR_antimono
            by auto
        }
        moreover {
          fix db
          assume "db \<in> set (linearize data_in)"
          then have "fst db < fst x"
            using snoc(4)
            by auto
          then have "\<not> (\<lambda>(t, _). memR (args_ivl args) (nt - t)) db"
            using mem memR_antimono
            by auto
        }
        ultimately have "lin_data_in''_mv (xs @ [x]) = []"
          using mem
          unfolding lin_data_in''_mv_def data_in'_eq
          by auto
        then have "False" using non_empty by auto
      }
      then have mem: "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<longrightarrow> (\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
        by auto

      have tuple_since_hist_mv_props: "(case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of
        None    \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx
       | Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx)"
      proof (cases "(idx_mid_mv (xs @ [x])) = (idx_oldest_mv (xs @ [x]))")
        case True
        then have "tuple_since_hist_mv (xs @ [x]) init_tuple = Mapping.empty"
          unfolding tuple_since_hist_mv_def
          by auto
        then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = None"
          by (simp add: Mapping.empty_def Mapping.lookup.abs_eq)
        moreover have "\<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
          using True snoc
          unfolding tuple_since_tp_def
          by auto
        ultimately show ?thesis by auto
      next

        case non_empty: False
        
        then have "tuple_since_hist_mv (xs @ [x]) init_tuple = fst (fold fold_op_f (xs @ [x]) init_tuple)"
          unfolding tuple_since_hist_mv_def
          by auto
        then have "tuple_since_hist_mv (xs @ [x]) init_tuple = fst (fold_op_f x tuple)"
          using fold_alt[of fold_op_f "xs" "x" init_tuple]
          unfolding tuple_def
          by auto              
        then have mapping_eq: "tuple_since_hist_mv (xs @ [x]) init_tuple = upd_set joined_mapping (\<lambda>_. (get_idx_move tuple)) ((relR x) - Mapping.keys joined_mapping)"
          using fold_IH_since_hist
          by auto
        
        have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
          using mem non_empty snoc(2)
          by auto

        have data_in''_eq: "(lin_data_in''_mv (xs @ [x])) = lin_data_in''_mv (xs) @ [(\<lambda>(t, l, y). (t, y)) x]"
          using mem
          unfolding lin_data_in''_mv_def
          by simp

        have data_in''_last: "last (lin_data_in''_mv (xs @ [x])) = (\<lambda>(t, l, y). (t, y)) x"
          using mem snoc(2)
          unfolding lin_data_in''_mv_def
          by (simp add: Suc_le_lessD take_Suc_conv_app_nth)

        show ?thesis
        proof (cases "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as")
          case None
          then have not_mem: "as \<notin> ((relR x) - Mapping.keys joined_mapping)"
            using mapping_eq
            by (metis Mapping_lookup_upd_set option.discI)
          then have "as \<notin> (relR x) \<or> as \<in> Mapping.keys joined_mapping"
            by auto
          moreover have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
            using not_mem mapping_eq
            by (metis Mapping_lookup_upd_set)
          ultimately have not_relR: "as \<notin> (relR x)"
            by (simp add: None keys_is_none_rep)
          {
            fix idx
            assume "idx < idx_mid_mv (xs @ [x])"
            then have "last (lin_data_in''_mv (xs @ [x])) \<in> set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x])))"
            proof -
              have "idx_oldest_mv (xs @ [x]) < idx_mid_mv (xs @ [x])"
                using snoc(2) non_empty by (metis le_add2 le_neq_implies_less)
              then have "idx - idx_oldest_mv (xs @ [x]) < length (lin_data_in''_mv (xs @ [x]))"
                using \<open>idx < idx_mid_mv (xs @ [x])\<close> snoc(2) by linarith
              then show ?thesis
                by (metis drop_eq_Nil last_drop last_in_set not_le)
            qed
            moreover have "as \<notin> snd (last (lin_data_in''_mv (xs @ [x])))"
            using not_relR data_in''_last
              unfolding relR_def
              by (simp add: case_prod_beta')
            ultimately have "\<not>(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y)"
              by fastforce
          }
          then have "\<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
            unfolding tuple_since_tp_def
            by auto
          then show ?thesis
            using None
            by simp
        next
          case (Some idx)

          have data_in_nonempty: "lin_data_in''_mv (xs @ [x]) \<noteq> []"
            using snoc(2) non_empty
            by auto

          have idx_oldest_eq: "idx_oldest_mv (xs @ [x]) = idx_oldest_mv (xs)"
            using mem
            unfolding idx_oldest_mv_def
            by auto
          
          show ?thesis
          proof (cases "idx_mid_mv xs = idx_oldest_mv xs")
            case True
            then have IH_none: "Mapping.lookup (tuple_since_hist_mv xs init_tuple) as = None"
              unfolding tuple_since_hist_mv_def
              by simp
            then have "\<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
              using IH_none IH(1)
              by auto

            have "(lin_data_in''_mv xs) = []"
              using mv_ln_eq True
              by (metis Ex_list_of_length append_Nil append_eq_append_conv length_append)
            then have data_in''_eq: "(lin_data_in''_mv (xs @ [x])) = [(\<lambda>(t, l, y). (t, y)) x]"
              using data_in''_eq
              by auto

            show ?thesis
            proof (cases "as \<in> (relR x - Mapping.keys joined_mapping)")
              case mem: True
              then have "as \<in> relR x" by auto
              then have relR: "as \<in> snd ((\<lambda>(t, l, y). (t, y)) x)"
                unfolding relR_def
                by (simp add: case_prod_beta')

              have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some (get_idx_move tuple)"
                using mapping_eq mem
                by (simp add: Mapping_lookup_upd_set)
              then have idx_eq: "idx = idx_mid_mv xs"
                using Some IH(2)
                unfolding get_idx_move_def tuple_def
                by auto
              then have "idx < idx_mid_mv (xs @ [x])"
                unfolding idx_mid_mv_def
                by auto
              moreover have idx_eq': "(idx_oldest_mv (xs @ [x])) = idx"
                using idx_oldest_eq True idx_eq
                by auto
              moreover have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y)"
                using idx_eq' data_in''_eq relR
                by auto
              ultimately have "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
                using data_in_nonempty
                unfolding tuple_since_tp_def
                by auto
              then show ?thesis using Some by auto
            next
              case False
              then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
                using mapping_eq
                by (metis Mapping_lookup_upd_set)
              then have "as \<in> relR x"
                unfolding joined_mapping_def
                by (metis Mapping_lookup_filter_Some_P Some)
              then have relR: "as \<in> snd ((\<lambda>(t, l, y). (t, y)) x)"
                unfolding relR_def
                by (simp add: case_prod_beta')

              have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup tuple_since_hist' as"
                using Mapping_lookup_filter_not_None Some lookup_eq
                unfolding joined_mapping_def
                by fastforce
              then have idx_leq: "idx \<le> idx_mid_mv xs"
                using IH(3) Some
                unfolding tuple_since_hist'_def tuple_def
                by (auto split: option.splits)
              then have "idx < idx_mid_mv (xs @ [x])"
                unfolding idx_mid_mv_def
                by auto
              moreover have idx_leq': "idx \<le> (idx_oldest_mv (xs @ [x]))"
                using idx_oldest_eq True idx_leq
                by auto
              moreover have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y)"
                using idx_leq' data_in''_eq relR
                by auto
              ultimately have "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
                using data_in_nonempty
                unfolding tuple_since_tp_def
                by auto
              then show ?thesis using Some by auto
            qed
          next
            case IH_nonempty: False
            moreover have idx_leq: "idx < idx_mid_mv (xs @ [x])"
            proof -
              show ?thesis
              proof (cases "as \<in> ((relR x) - Mapping.keys joined_mapping)")
                case True
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some (get_idx_move tuple)"
                  using mapping_eq
                  by (simp add: Mapping_lookup_upd_set)
                then have "idx = get_idx_move tuple"
                  using Some
                  by auto
                then have "idx = idx_mid_mv xs"
                  using IH(2)
                  unfolding tuple_def
                  by auto
                then show ?thesis
                  unfolding idx_mid_mv_def
                  by auto
              next
                case False
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
                  using mapping_eq
                  by (metis Mapping_lookup_upd_set)
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup tuple_since_hist' as"
                  unfolding joined_mapping_def
                  using Some Mapping_lookup_filter_not_None
                  by force
                then have "Mapping.lookup (fst (fold fold_op_f xs init_tuple)) as = Some idx"
                  unfolding tuple_since_hist'_def tuple_def
                  using Some
                  by auto
                then have "tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
                  using IH(1) IH_nonempty
                  unfolding tuple_since_hist_mv_def
                  by auto
                then have "idx \<le> idx_mid_mv xs"
                  unfolding tuple_since_tp_def
                  by auto
                then show ?thesis unfolding idx_mid_mv_def by auto
              qed
            qed
            moreover have "\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y"
            proof -
              show ?thesis
              proof (cases "as \<in> ((relR x) - Mapping.keys joined_mapping)")
                case True
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some (get_idx_move tuple)"
                  using mapping_eq
                  by (simp add: Mapping_lookup_upd_set)
                then have "idx = get_idx_move tuple"
                  using Some
                  by auto
                then have "idx + 1 = idx_mid_mv (xs @ [x])"
                  using IH(2)
                  unfolding tuple_def idx_mid_mv_def
                  by auto
                then have "idx + 1 = length (lin_data_in''_mv (xs @ [x])) + idx_oldest_mv (xs @ [x])"
                  using snoc(2)
                  by linarith
                then have "drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x])) = [(\<lambda>(t, l, y). (t, y)) x]"
                  using data_in''_last drop_last[of "lin_data_in''_mv (xs @ [x])"] data_in_nonempty
                  by (simp add: data_in''_eq)
                moreover have "as \<in> (relR x)"
                  using True
                  by auto
                ultimately show ?thesis
                  unfolding relR_def
                  by (auto simp add: case_prod_beta')
              next
                case not_mem: False
                then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
                    using not_mem mapping_eq
                    by (metis Mapping_lookup_upd_set)
                have "as \<notin> (relR x) \<or> as \<in> Mapping.keys joined_mapping" using not_mem by auto
                moreover {
                  assume "as \<notin> (relR x)"
                  then have "Mapping.lookup joined_mapping as = None"
                    unfolding joined_mapping_def
                    using Mapping_keys_filterD keys_dom_lookup
                    by fastforce
                  then have "False" using lookup_eq Some by auto
                }
                ultimately have "as \<in> Mapping.keys joined_mapping" by blast
                then have relR: "as \<in> relR x"
                  unfolding joined_mapping_def
                  by (meson Mapping_keys_filterD)
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup tuple_since_hist' as"
                  using lookup_eq
                  unfolding joined_mapping_def
                  by (simp add: Mapping_lookup_filter_Some)
                then have "tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
                  using IH(1) Some IH_nonempty
                  unfolding tuple_since_hist'_def tuple_def tuple_since_hist_mv_def
                  by (auto split: option.splits)
                then have IH_hist: "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv xs) (lin_data_in''_mv xs)). as \<in> y)"
                  unfolding tuple_since_tp_def
                  by (auto)
                have "idx_oldest_mv (xs @ [x]) = idx_oldest_mv (xs)"
                  using mem
                  unfolding idx_oldest_mv_def
                  by auto
                moreover have "lin_data_in''_mv (xs @ [x]) = (lin_data_in''_mv (xs)) @ [(\<lambda>(t, l, y). (t, y)) x]"
                  using mem
                  unfolding lin_data_in''_mv_def
                  by auto
                moreover have "(idx - idx_oldest_mv (xs @ [x])) < length (lin_data_in''_mv (xs @ [x]))"
                  using idx_leq snoc(2) non_empty
                  by linarith
                ultimately have list_eq: "drop (idx - idx_oldest_mv xs) (lin_data_in''_mv xs) @ [(\<lambda>(t, l, y). (t, y)) x] = (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x])))"
                  by auto

                have "as \<in> snd ((\<lambda>(t, l, y). (t, y)) x)"
                  using relR
                  unfolding relR_def
                  by (auto simp add: case_prod_beta')
                then have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv xs) (lin_data_in''_mv xs) @ [(\<lambda>(t, l, y). (t, y)) x]). as \<in> y)"
                  using IH_hist
                  by auto

                then show ?thesis
                  using list_eq
                  by auto
              qed
            qed
            moreover have "idx_oldest_mv (xs @ [x]) < idx \<Longrightarrow> as \<notin> snd (lin_data_in''_mv (xs @ [x]) ! (idx - idx_oldest_mv (xs @ [x]) - 1))"
            proof -
              assume assm: "idx_oldest_mv (xs @ [x]) < idx"
              then have "idx_oldest_mv (xs) < idx" using idx_oldest_eq by auto
              show ?thesis
              proof (cases "as \<in> ((relR x) - Mapping.keys joined_mapping)")
                case True
                then have "as \<in> relR x" "as \<notin> Mapping.keys joined_mapping" by auto
                then have "Mapping.lookup tuple_since_hist' as = None"
                  unfolding joined_mapping_def
                  by (meson Mapping_keys_filterI option.exhaust)
                then have tuple_since_tp: "\<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
                  using IH(1) IH_nonempty
                  unfolding tuple_since_hist'_def tuple_def tuple_since_hist_mv_def
                  by auto
                have len: "length (lin_data_in''_mv xs) + (idx_oldest_mv xs) = (idx_mid_mv xs)"
                  using mv_ln_eq
                  by auto
                then have IH_nonempty: "lin_data_in''_mv xs \<noteq> []"
                  using IH_nonempty
                  by auto
                then have not_relR: "as \<notin> snd (last (lin_data_in''_mv xs))"
                  using no_hist_last_not_sat[OF len tuple_since_tp]
                  by auto
                
                have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some (get_idx_move tuple)"
                  using True mapping_eq
                  by (simp add: Mapping_lookup_upd_set)
                then have idx_eq: "idx = idx_mid_mv xs"
                  using IH(2) Some
                  unfolding tuple_def 
                  by auto
                moreover have idx_mid_eq: "idx_mid_mv xs + 1 = idx_mid_mv (xs @ [x])"
                  using mem
                  unfolding idx_mid_mv_def
                  by auto
                ultimately have idx_rel: "(idx - idx_oldest_mv (xs @ [x]) - 1) = (idx_mid_mv (xs @ [x]) - idx_oldest_mv (xs @ [x]) - 2)"
                  by auto
                moreover have "idx_mid_mv (xs @ [x]) - idx_oldest_mv (xs @ [x]) - 1 \<le> length (lin_data_in''_mv (xs))"
                proof -
                  have "length (lin_data_in''_mv xs) + (idx_oldest_mv (xs @ [x])) + 1 = idx_mid_mv (xs @ [x])"
                    using len idx_oldest_eq idx_mid_eq
                    by auto
                  then show ?thesis by auto
                qed
                ultimately have "lin_data_in''_mv (xs @ [x]) ! (idx - idx_oldest_mv (xs @ [x]) - 1) = lin_data_in''_mv (xs) ! (idx_mid_mv (xs @ [x]) - idx_oldest_mv (xs @ [x]) - 2)"
                  using data_in''_eq idx_append[of "idx_mid_mv (xs @ [x]) - idx_oldest_mv (xs @ [x]) - 2" "lin_data_in''_mv (xs)" "(\<lambda>(t, l, y). (t, y)) x"]
                  using idx_eq idx_oldest_eq assm len
                  by auto
                then have "lin_data_in''_mv (xs @ [x]) ! (idx - idx_oldest_mv (xs @ [x]) - 1) = lin_data_in''_mv (xs) ! (idx_mid_mv (xs) - idx_oldest_mv (xs) - 1)"
                  using idx_oldest_eq idx_mid_eq len idx_rel idx_eq
                  by auto
                moreover have "lin_data_in''_mv (xs) ! (idx_mid_mv (xs) - idx_oldest_mv (xs) - 1) = last (lin_data_in''_mv (xs))"
                  using len IH_nonempty
                  by (metis add_diff_cancel_right' last_conv_nth)
                ultimately show ?thesis using not_relR by auto
              next
                case not_mem: False
                then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
                  using mapping_eq
                  by (metis Mapping_lookup_upd_set)
                then have relR: "as \<in> relR x"
                  unfolding joined_mapping_def
                  by (metis Mapping_lookup_filter_Some_P Some)
                then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup tuple_since_hist' as"
                  using Mapping_lookup_filter_not_None Some lookup_eq
                  unfolding joined_mapping_def
                  by fastforce
                then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup (fst (fold fold_op_f xs init_tuple)) as"
                  unfolding tuple_since_hist'_def tuple_def
                  by auto
                then have "tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
                  using IH(1) IH_nonempty Some
                  unfolding tuple_since_hist_mv_def
                  by (auto split: option.splits)
                then have idx_props:
                  "idx < idx_mid_mv xs"
                  "idx > idx_oldest_mv xs \<longrightarrow> as \<notin> snd (lin_data_in''_mv xs ! (idx - idx_oldest_mv xs - 1))"
                  unfolding tuple_since_tp_def
                  by auto
                then have "as \<notin> snd (lin_data_in''_mv xs ! (idx - idx_oldest_mv (xs @ [x]) - 1))"
                  using assm idx_oldest_eq
                  by auto
                moreover have "idx - idx_oldest_mv (xs @ [x]) - 1 < length (lin_data_in''_mv xs)"
                  using assm idx_oldest_eq idx_props(1) mv_ln_eq less_diff_conv2
                  by auto
                ultimately show ?thesis
                  using idx_append[of "idx - idx_oldest_mv (xs @ [x]) - 1" "lin_data_in''_mv xs" "(\<lambda>(t, l, y). (t, y)) x"]
                        data_in''_eq
                  by auto
              qed
            qed
            ultimately have "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
              using data_in_nonempty
              unfolding tuple_since_tp_def
              by auto
            then show ?thesis using Some by auto
          qed
        qed
      qed
      moreover have hist_sat_props: "as \<in> (hist_sat_mv (xs @ [x]) init_tuple) =
        (((lin_data_in''_mv (xs @ [x])) \<noteq> []) \<and> (
          \<forall>(t, r) \<in> set (lin_data_in''_mv (xs @ [x])). as \<in> r
        ))"
      proof -
        have fold_eq: "(fst \<circ> snd) (fold fold_op_f (xs @ [x]) init_tuple) = (fst \<circ> snd) (fold_op_f x tuple)"
          using fold_alt[of fold_op_f xs x init_tuple]
          unfolding tuple_def
          by auto
        
        show "as \<in> (hist_sat_mv (xs @ [x]) init_tuple) =
        (((lin_data_in''_mv (xs @ [x])) \<noteq> []) \<and> (
          \<forall>(t, r) \<in> set (lin_data_in''_mv (xs @ [x])). as \<in> r
        ))"
        proof (cases "lin_data_in''_mv (xs @ [x]) = []")
          case True
          show ?thesis
          proof (rule iffI)
            assume "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
            then have "False" using True unfolding hist_sat_mv_def by auto
            then show "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
              by auto
          next
            assume "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
            then have "False" using True by auto
            then show "as \<in> hist_sat_mv (xs @ [x]) init_tuple" by auto
          qed
        next
          case non_empty: False
          show ?thesis
          proof (cases "lin_data_in''_mv xs = []")
            case True
            {
              assume "\<not>(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
              then have "(\<lambda>(t, _). \<not>memR (args_ivl args) (nt - t)) x" by auto
              then have "lin_data_in''_mv (xs @ [x]) = []"
                using True
                unfolding lin_data_in''_mv_def
                by auto
              then have "False" using non_empty by auto
            }
            then have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
              by blast
            then have lin_eq: "lin_data_in''_mv (xs @ [x]) = [(\<lambda>(t, l, r). (t, r)) x]"
              using True
              unfolding lin_data_in''_mv_def
              by auto

            show ?thesis
            proof (rule iffI)
              assume "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
              then have "as \<in> (((fst \<circ> snd) (fold fold_op_f xs init_tuple) \<inter> relR x) \<union> {as \<in> (snd o snd) x. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])})"
                using lin_eq fold_alt[of fold_op_f xs x init_tuple] fold_IH_hist_sat
                unfolding hist_sat_mv_def tuple_def hist_sat'_def
                by (auto split: list.splits simp add: case_prod_beta')
              moreover {
                assume "as \<in> ((fst \<circ> snd) (fold fold_op_f xs init_tuple) \<inter> relR x)"
                then have "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                  unfolding relR_def
                  by (auto simp add: case_prod_beta')
                then have "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                  using lin_eq
                  by auto
              }
              moreover {
                assume "as \<in> {as \<in> (snd o snd) x. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])}"
                then have "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                  by (auto simp add: case_prod_beta')
                then have "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                  using lin_eq
                  by auto
              }
              ultimately show "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                by auto
            next
              assume assm: "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
              then have tp: "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) (idx_oldest_mv (xs @ [x]))"
                using mv_ln_eq
                unfolding tuple_since_tp_def
                by (metis add_diff_cancel_right' in_set_dropD length_greater_0_conv less_irrefl zero_less_diff)
              have len: "length (lin_data_in''_mv (xs @ [x])) + idx_oldest_mv (xs @ [x]) = idx_mid_mv (xs @ [x])"
                using mv_ln_eq
                by auto
              obtain idx where "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some idx \<and> idx \<le> idx_oldest_mv (xs @ [x])"
                using tuple_since_hist_lookup_leq[OF tuple_since_hist_mv_props tp len]
                by auto
              moreover have relR: "as \<in> relR x"
                using assm lin_eq
                unfolding relR_def
                by (auto simp add: case_prod_beta')
              ultimately have "as \<in> {as \<in> (snd o snd) x. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])}"
                unfolding relR_def
                by auto
              then show "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
                using lin_eq relR
                unfolding hist_sat_mv_def relR_def
                by (auto split: list.splits simp add: case_prod_beta')
            qed
          next
            case False
            show ?thesis
            proof (rule iffI)
              assume assm: "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
              then obtain db dbs where db_props: "db#dbs = lin_data_in''_mv (xs @ [x])"
                unfolding hist_sat_mv_def
                by (auto split: list.splits)
              then have "as \<in> ((fst \<circ> snd) (fold_op_f x tuple) \<union> {as \<in> snd db. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])})"
                using assm fold_eq
                unfolding hist_sat_mv_def
                by (auto split: list.splits)
              moreover {
                assume as_mem: "as \<in> (fst \<circ> snd) (fold_op_f x tuple)"
                then have as_props:
                    "as \<in> hist_sat'"
                    "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                  using fold_IH_hist_sat
                  unfolding relR_def
                  by (auto simp add: case_prod_beta')
                moreover have "(\<forall>(t, r)\<in>set (lin_data_in''_mv xs). as \<in> r)"
                  using as_props(1) IH(4) False
                  unfolding hist_sat_mv_def hist_sat'_def tuple_def
                  by (auto split: list.splits)
                ultimately have "\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r"
                  unfolding lin_data_in''_mv_def
                  by auto
              }
              moreover {
                assume "as \<in> {as \<in> snd db. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])}"
                then obtain idx where idx_props: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some idx" "idx \<le> idx_oldest_mv (xs @ [x])"
                  by (auto split: option.splits)
                then have "\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y"
                  using tuple_since_hist_mv_props
                  unfolding tuple_since_tp_def
                  by auto
                then have "\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r"
                  using idx_props(2)
                  by auto
              }
              ultimately have "\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r" by auto
  
              then show "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                using db_props
                by auto
            next
              assume assm: "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
              then have tp: "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) (idx_oldest_mv (xs @ [x]))"
                using mv_ln_eq
                unfolding tuple_since_tp_def
                by (metis add_diff_cancel_right' in_set_dropD length_greater_0_conv less_irrefl zero_less_diff)
              have len: "length (lin_data_in''_mv (xs @ [x])) + idx_oldest_mv (xs @ [x]) = idx_mid_mv (xs @ [x])"
                using mv_ln_eq
                by auto
              obtain idx where idx_props: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some idx \<and> idx \<le> idx_oldest_mv (xs @ [x])"
                using tuple_since_hist_lookup_leq[OF tuple_since_hist_mv_props tp len]
                by auto
              then have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
                using mem non_empty snoc(2)
                by auto
              then have relR: "as \<in> relR x"
                using assm
                unfolding relR_def lin_data_in''_mv_def
                by (auto simp add: case_prod_beta')
              then have "as \<in> {as \<in> (snd o snd) x. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])}"
                using idx_props
                unfolding relR_def
                by auto
              then show "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
                using assm
                unfolding hist_sat_mv_def
                by (auto split: list.splits simp add: case_prod_beta')
            qed
          qed
        qed
      qed
      (* fold_IH_since_sat *)
      moreover have "(as \<in> since_sat_mv (xs @ [x]) init_tuple \<longrightarrow> as \<in> hist_sat_mv (xs @ [x]) init_tuple \<or> tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args (lin_data_in''_aux_mv (xs @ [x])))"
      proof -
        {
          assume assm: "as \<in> since_sat_mv (xs @ [x]) init_tuple"
          then have non_empty: "lin_data_in''_mv (xs @ [x]) \<noteq> []"
            using mv_ln_eq
            unfolding since_sat_mv_def
            by (metis comm_monoid_add_class.add_0 equals0D length_nth_simps(1))
          then have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
            using mem
            by auto

          have "as \<in> (snd \<circ> snd \<circ> snd) (fold fold_op_f (xs @ [x]) init_tuple)"
            using assm
            unfolding since_sat_mv_def
            by (auto split: if_splits)

          then have "as \<in> (snd \<circ> snd \<circ> snd) (fold_op_f x (fold fold_op_f xs init_tuple))"
            using fold_alt[of fold_op_f xs x init_tuple]
            by auto
          then have as_mem: "as \<in> (since_sat' \<inter> relR x) \<union> {as \<in> relR x. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as (relL x)}"
            using fold_IH_since_sat
            unfolding tuple_def
            by auto

          have " as \<in> hist_sat_mv (xs @ [x]) init_tuple \<or> tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args (lin_data_in''_aux_mv (xs @ [x]))"
          proof (cases "as \<in> (since_sat' \<inter> relR x)")
            case True
            then have relR: "as \<in> relR x" by auto
            then show ?thesis
            proof (cases "lin_data_in''_mv xs = []")
              case empty: True
              then have "lin_data_in''_mv (xs @ [x]) = [(\<lambda>(t, l, r). (t, r)) x]"
                using mem
                unfolding lin_data_in''_mv_def
                by auto
              moreover have "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                using relR
                unfolding relR_def
                by (simp add: case_prod_beta)
              ultimately have "(\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                by auto
              then have "as \<in> (hist_sat_mv (xs @ [x]) init_tuple)"
                using non_empty hist_sat_props
                by auto
              then show ?thesis by auto
            next
              case IH_nonempty: False
              then have "idx_mid_mv xs \<noteq> idx_oldest_mv xs"
                using mv_ln_eq
                by (metis add_cancel_left_left length_0_conv)
              then have "as \<in> hist_sat_mv xs init_tuple \<or> tuple_since_lhs as (lin_data_in''_mv xs) args (lin_data_in''_aux_mv xs)"
                using True IH(5) IH_nonempty
                unfolding since_sat'_def tuple_def since_sat_mv_def
                by (auto split: if_splits)
              moreover {
                assume "as \<in> hist_sat_mv xs init_tuple"
                then have "\<forall>(t, r)\<in>set (lin_data_in''_mv xs). as \<in> r"
                  using IH(4)
                  by auto
                moreover have "lin_data_in''_mv (xs @ [x]) = lin_data_in''_mv xs @ [(\<lambda>(t, l, r). (t, r)) x]"
                  using mem
                  unfolding lin_data_in''_mv_def
                  by auto
                moreover have "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                  using relR
                  unfolding relR_def
                  by (simp add: case_prod_beta)
                ultimately have "\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r"
                  by auto
                then have "as \<in> (hist_sat_mv (xs @ [x]) init_tuple)"
                  using non_empty hist_sat_props
                  by auto
                then have ?thesis by auto
              }
              moreover {
                assume "tuple_since_lhs as (lin_data_in''_mv xs) args (lin_data_in''_aux_mv xs)"
                then obtain n where n_props:
                  "n\<in>{0..<length (lin_data_in''_mv xs)}"
                  "\<forall>(t, l, y)\<in>set (drop n (lin_data_in''_aux_mv xs)). as \<in> y"
                  "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv xs)))) (restrict (args_L args) (args_R args) as)"
                  unfolding tuple_since_lhs_def
                  by (auto simp add: Let_def)
                have n_l: "n < length (lin_data_in''_aux_mv xs)"
                  using n_props(1) data_in''_aux_eq
                  by (metis atLeastLessThan_iff length_map)
                then have drop_eq: "drop n (lin_data_in''_aux_mv (xs @ [x])) = drop n (lin_data_in''_aux_mv xs) @ [x]"
                  using mem
                  unfolding lin_data_in''_aux_mv_def
                  by auto
                then have all_relR: "\<forall>(t, l, y)\<in>set (drop n (lin_data_in''_aux_mv (xs @ [x]))). as \<in> y"
                  using n_props(2) relR
                  unfolding lin_data_in''_aux_mv_def relR_def
                  by auto

                have "hd (drop n (lin_data_in''_aux_mv xs)) = hd (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                  using n_l drop_eq hd_append[of "drop n (lin_data_in''_aux_mv xs)" "[x]"]
                  by auto
                then have "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv (xs @ [x]))))) (restrict (args_L args) (args_R args) as)"
                  using n_props(3)
                  by auto
                then have "let suffix = drop n (lin_data_in''_aux_mv (xs @ [x])) in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) as)"
                  using non_empty all_relR
                  by auto
                moreover have "n\<in>{0..<length (lin_data_in''_mv (xs @ [x]))}"
                  using n_props(1)
                  unfolding lin_data_in''_mv_def
                  by auto
                ultimately have "tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args (lin_data_in''_aux_mv (xs @ [x]))"
                  using non_empty
                  unfolding tuple_since_lhs_def
                  by blast
                then have ?thesis by auto
              }
              ultimately show ?thesis by blast
            qed
          next
            case False
            then have as_mem: "as \<in> {as \<in> relR x. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as (relL x)}"
              using as_mem
              by auto
            then have
              "as \<in> relR x"
              "proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as (relL x)"
              by auto
            then have x_props:
              "as \<in> relR x"
              "join_cond (args_pos args) (relL x) (restrict (args_L args) (args_R args) as)"
              unfolding proj_tuple_in_join_def
              by auto
            define n where "n = length (lin_data_in''_aux_mv (xs @ [x])) - 1"
            then have drop_eq: "drop n (lin_data_in''_aux_mv (xs @ [x])) = [x]"
              using mem
              unfolding lin_data_in''_aux_mv_def
              by auto
            then have "\<forall>(t, l, y)\<in>set (drop n (lin_data_in''_aux_mv (xs @ [x]))). as \<in> y"
              using x_props(1)
              unfolding relR_def
              by auto
            moreover have "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv (xs @ [x]))))) (restrict (args_L args) (args_R args) as)"
              using drop_eq x_props(2)
              by auto
            ultimately have "(let suffix = drop n (lin_data_in''_aux_mv (xs @ [x])) in
              (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and>
              join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) as)
            )"
              by auto
            moreover have "n\<in>{0..<length (lin_data_in''_mv (xs @ [x]))}"
              using n_def non_empty data_in''_aux_eq
              by (metis (no_types, lifting) One_nat_def atLeastLessThan_iff diff_Suc_less length_greater_0_conv length_map zero_le)
            ultimately have "tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args (lin_data_in''_aux_mv (xs @ [x]))"
              using non_empty
              unfolding tuple_since_lhs_def
              by blast
            then show ?thesis by auto
          qed
        }
        then show ?thesis by auto
      qed
      moreover have "(tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args (lin_data_in''_aux_mv (xs @ [x])) \<longrightarrow> as \<in> since_sat_mv (xs @ [x]) init_tuple)"
      proof -
        {
          assume assm: "tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args (lin_data_in''_aux_mv (xs @ [x]))"
          then have non_empty: "lin_data_in''_mv (xs @ [x]) \<noteq> []"
            unfolding tuple_since_lhs_def
            by auto
          then have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
            using mem
            by auto
          obtain n where n_props:
            "n\<in>{0..<length (lin_data_in''_mv (xs @ [x]))}"
            "(\<forall>(t, l, r)\<in>set (drop n (lin_data_in''_aux_mv (xs @ [x]))). as \<in> r)"
            "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv (xs @ [x]))))) (restrict (args_L args) (args_R args) as)"
            using assm 
            unfolding tuple_since_lhs_def
            by (auto simp add: Let_def)
          
          have "as \<in> (since_sat' \<inter> relR x) \<union> {as \<in> relR x. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as (relL x)}"
          proof (cases "lin_data_in''_mv xs = []")
            case True
            then have lin_data_in''_eq: "lin_data_in''_mv (xs @ [x]) = [(\<lambda>(t, l, r). (t, r)) x]"
              using mem
              unfolding lin_data_in''_mv_def
              by auto
            then have "lin_data_in''_aux_mv (xs @ [x]) = [x]"
              using True data_in''_aux_eq data_in'_aux_eq mem
              unfolding lin_data_in''_aux_mv_def lin_data_in''_mv_def
              by auto
            then have
              "as \<in> relR x"
              "join_cond (args_pos args) (relL x) (restrict (args_L args) (args_R args) as)"
              using n_props lin_data_in''_eq
              unfolding relR_def
              by auto
            then have "as \<in> {as \<in> relR x. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as (relL x)}"
              unfolding proj_tuple_in_join_def
              by auto
            then show ?thesis by auto
          next
            case False
            
            {
              assume n_l: "n\<in>{0..<length (lin_data_in''_mv xs)}"
              {
                fix t l r
                assume "(t, l, r)\<in>set (drop n (lin_data_in''_aux_mv (xs)))"
                then have "(t, l, r)\<in>set (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                  unfolding lin_data_in''_aux_mv_def
                  by auto
              }
              then have relR:
                "(\<forall>(t, l, r)\<in>set (drop n (lin_data_in''_aux_mv (xs))). as \<in> r)"
                using n_props(2)
                by blast

              have "hd (drop n (lin_data_in''_aux_mv (xs @ [x]))) = hd (drop n ((data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs) @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) [x]))"
                unfolding lin_data_in''_aux_mv_def
                by auto
              moreover have "length (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs) \<ge> n"
                using n_l data_in'_aux_eq
                unfolding lin_data_in''_mv_def
                by (metis atLeastLessThan_iff data_in''_aux_eq length_map less_imp_le_nat lin_data_in''_aux_mv_def n_l)
              ultimately have "hd (drop n (lin_data_in''_aux_mv (xs @ [x]))) = hd (drop n (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs) @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) [x])"
                using n_l drop_append[of n "(data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs)" "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) [x]"]
                by auto
              moreover have "drop n (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs) \<noteq> []"
                using False data_in''_aux_eq n_l
                unfolding lin_data_in''_aux_mv_def lin_data_in''_mv_def
                by (metis (no_types, lifting) atLeastLessThan_iff length_drop length_map length_nth_simps(1) not_less0 zero_less_diff)
              ultimately have "hd (drop n (lin_data_in''_aux_mv (xs @ [x]))) = hd (drop n (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs))"
                using hd_append[of "drop n (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs)" "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) [x]"]
                by auto
              then have "hd (drop n (lin_data_in''_aux_mv xs)) = hd (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                unfolding lin_data_in''_aux_mv_def
                by auto
              then have "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv xs)))) (restrict (args_L args) (args_R args) as)"
                using n_props(3)
                by auto

              then have "(let suffix = drop n (lin_data_in''_aux_mv xs) in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) as))"
                using relR
                by auto
              then have "tuple_since_lhs as (lin_data_in''_mv xs) args (lin_data_in''_aux_mv xs)"
                using n_l False
                unfolding tuple_since_lhs_def
                by blast
              then have "as \<in> (snd \<circ> snd \<circ> snd) (fold fold_op_f xs init_tuple)"
                using IH(6) mv_ln_eq False
                unfolding since_sat_mv_def
                by (meson equals0D)
              then have "as \<in> since_sat'"
                unfolding since_sat'_def tuple_def
                by auto
              moreover have "as \<in> relR x"
              proof -
                have "n < length (lin_data_in''_aux_mv (xs @ [x]))"
                  using n_props(1) data_in'_aux_eq
                  unfolding lin_data_in''_aux_mv_def lin_data_in''_mv_def
                  using length_map[of "\<lambda>(t, l, y). (t, y)" "(filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (xs @ [x]))"]
                  proof -
                    show "n < length (data_in'_aux @ filter (\<lambda>(n, p). memR (args_ivl args) (nt - n)) (xs @ [x]))"
                      by (metis atLeastLessThan_iff data_in''_aux_eq length_map lin_data_in''_aux_mv_def n_props(1))
                  qed
                then have "x \<in> set (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                  using mem
                  unfolding lin_data_in''_aux_mv_def
                  by auto
                then show ?thesis using n_props(2) unfolding relR_def by auto
              qed
              ultimately have "as \<in> (since_sat' \<inter> relR x) \<union> {as \<in> relR x. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as (relL x)}"
                by auto
            }
            moreover {
              assume "n \<notin> {0..<length (lin_data_in''_mv xs)}"
              then have "n\<in>{length (lin_data_in''_mv xs)..<length (lin_data_in''_mv (xs @ [x]))}"
                using n_props(1)
                by auto
              moreover have "length (lin_data_in''_mv (xs @ [x])) = length (lin_data_in''_mv (xs)) + 1"
                using mem
                unfolding lin_data_in''_mv_def
                by auto
              ultimately have "n = length (lin_data_in''_mv xs)"
                by auto
              then have n_eq: "n = length (lin_data_in''_aux_mv xs)"
                using data_in''_aux_eq
                by (metis length_map)
              then have
                "(hd (drop n (lin_data_in''_aux_mv (xs @ [x])))) = x"
                "x \<in> set (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                using mem
                unfolding lin_data_in''_aux_mv_def
                by auto
              then have
                "as \<in> relR x"
                "join_cond (args_pos args) (relL x) (restrict (args_L args) (args_R args) as)"
                using n_props(2-3)
                unfolding relR_def
                by auto
              then have "as \<in> {as \<in> relR x. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as (relL x)}"
                unfolding proj_tuple_in_join_def
                by auto
            }
            ultimately show ?thesis by blast
          qed
          then have "as \<in> (snd \<circ> snd \<circ> snd) (fold_op_f x (fold fold_op_f xs init_tuple))"
            using fold_IH_since_sat
            unfolding tuple_def
            by auto
          then have "as \<in> (snd \<circ> snd \<circ> snd) (fold fold_op_f (xs @ [x]) init_tuple)"
            using fold_alt[of fold_op_f xs x init_tuple]
            by auto
          then have "as \<in> since_sat_mv (xs @ [x]) init_tuple"
            using mv_ln_eq non_empty
            unfolding since_sat_mv_def since_sat'_def tuple_def
            by (metis add_cancel_left_left length_0_conv)
        }
        then show ?thesis by auto
      qed
      moreover have "get_idx_move (fold fold_op_f (xs @ [x]) init_tuple) = idx_mid_mv (xs @ [x])"
      proof -
        have "fold fold_op_f (xs @ [x]) init_tuple = fold_op_f x tuple"
          using fold_alt[of fold_op_f "xs" "x" init_tuple]
          unfolding tuple_def
          by auto
        moreover have "get_idx_move (fold_op_f x tuple) = (get_idx_move tuple) + 1"
          unfolding get_idx_move_def fold_op_f_def
          by (simp add: Let_def case_prod_beta)
        moreover have "(get_idx_move tuple) + 1 = idx_mid_mv (xs @ [x])"
          using IH(2)
          unfolding tuple_def idx_mid_mv_def
          by auto
        ultimately show ?thesis by auto
      qed
      moreover have "(case Mapping.lookup (fst (fold fold_op_f (xs @ [x]) init_tuple)) as of None \<Rightarrow> True | Some idx \<Rightarrow> idx < idx_mid_mv (xs @ [x]))"
      proof -
        have "fold fold_op_f (xs @ [x]) init_tuple = fold_op_f x (fold fold_op_f xs init_tuple)"
          using fold_alt[of fold_op_f xs x init_tuple]
          by auto
        then have mapping_eq: "fst (fold fold_op_f (xs @ [x]) init_tuple) = upd_set joined_mapping (\<lambda>_. get_idx_move tuple) (relR x - Mapping.keys joined_mapping)"
          using fold_IH_since_hist
          unfolding tuple_def
          by auto
        show ?thesis
        proof (cases "Mapping.lookup (fst (fold fold_op_f (xs @ [x]) init_tuple)) as")
          case (Some idx)
          then show ?thesis
          proof (cases "as \<in> (relR x - Mapping.keys joined_mapping)")
            case True
            then have "idx = get_idx_move tuple"
              using Some mapping_eq
              by (simp add: Mapping_lookup_upd_set)
            then show ?thesis
              using IH(2-3) Some
              unfolding tuple_def idx_mid_mv_def
              by auto
          next
            case False
            then have "Mapping.lookup (fst (fold fold_op_f (xs @ [x]) init_tuple)) as = Mapping.lookup joined_mapping as"
              using mapping_eq
              by (metis Mapping_lookup_upd_set)
            then have "Mapping.lookup (fst (fold fold_op_f (xs @ [x]) init_tuple)) as = Mapping.lookup tuple_since_hist' as"
              unfolding joined_mapping_def
              using Some Mapping_lookup_filter_not_None
              by fastforce
            then show ?thesis
              unfolding tuple_since_hist'_def tuple_def
              using IH(3) Some idx_mid_mv_def
              by auto
          qed
        qed (auto)
      qed
      ultimately show ?case by auto
    qed
    moreover have is_empty_eq: "(idx_mid_mv move = idx_oldest_mv move) = Queue.is_empty data_in''"
      using mv_idx_mid' mv_idx_oldest' data_in''_len' Queue.is_empty_alt[of data_in'']
      by auto
    moreover have since_hist''_eq: "tuple_since_hist_mv move init_tuple = tuple_since_hist''"
      using is_empty_eq fold_tuple_res
      unfolding tuple_since_hist''_def tuple_since_hist_mv_def init_tuple_def
      by (metis fst_conv)
    moreover have "hist_sat_mv move init_tuple = hist_sat''"
    proof -
      have hist_sat'_eq: "(fst \<circ> snd) (fold fold_op_f move init_tuple) = hist_sat'"
        using fold_tuple_res
        unfolding init_tuple_def
        by (metis comp_apply fst_conv snd_conv)
      {
        fix x
        assume assm: "x \<in> hist_sat_mv move init_tuple"
        then obtain db dbs where db_props: "db#dbs = linearize data_in''"
          unfolding hist_sat_mv_def mv_data_in''
          by (auto split: list.splits)
        then have lin_non_empty: "linearize (data_in'') \<noteq> []"
          by auto
        then have non_empty: "\<not> Queue.is_empty (data_in'')"
          using Queue.is_empty_alt
          by auto

        have hd_in: "hd (linearize data_in'') = db"
          using db_props mv_data_in''
          by (metis list.sel(1))

        obtain dbs' where safe_hd_eq: "safe_hd data_in'' = (Some db, dbs')"
        proof (cases "safe_hd data_in''")
          case (Pair hd_opt dbs')
          moreover have "hd_opt = Some db"
            using safe_hd_rep[OF Pair] lin_non_empty hd_in
            by (cases hd_opt) simp_all
          ultimately have "safe_hd data_in'' = (Some db, dbs')"
            by simp
          then show ?thesis
            by (rule that)
        qed
        
        have "x \<in> (fst \<circ> snd) (fold fold_op_f move init_tuple) \<union> {as \<in> snd db. case Mapping.lookup tuple_since_hist'' as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest'}"
          using db_props assm since_hist''_eq mv_idx_oldest' mv_data_in''
          unfolding hist_sat_mv_def
          by (auto split: list.splits)
        then have "x \<in> hist_sat' \<union> {as \<in> snd db. case Mapping.lookup tuple_since_hist'' as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest'}"
          using hist_sat'_eq
          by auto
        moreover have "fst (safe_hd data_in'') = Some db"
          using safe_hd_eq
          by auto
        ultimately have "x \<in> hist_sat''"
          using hist_sat''_def
          by auto
      }
      moreover {
        fix x
        assume assm: "x \<in> hist_sat''"
        then have "fst (safe_hd data_in'') \<noteq> None"
          unfolding hist_sat''_def
          by (cases "fst (safe_hd data_in'')") simp_all
        then obtain db dbs' where safe_hd_eq:
          "safe_hd data_in'' = (Some db, dbs')"
          by (metis not_None_eq prod.collapse)
        then have x_mem: "x \<in> hist_sat' \<union> {tuple \<in> snd db. case Mapping.lookup tuple_since_hist'' tuple of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest'}"
          using assm
          unfolding hist_sat''_def
          by auto
        have hd_props:
          "linearize data_in'' \<noteq> []"
          "db = hd (linearize data_in'')"
          using safe_hd_eq safe_hd_rep[of data_in'' "Some db" dbs']
          by auto
        then obtain dbs where dbs_props: "linearize data_in'' = db#dbs"
          by (metis hd_Cons_tl)
        have "x \<in> (fst \<circ> snd) (fold fold_op_f move init_tuple) \<union> {as \<in> snd db. case Mapping.lookup (tuple_since_hist_mv move init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv move}"
          using x_mem mv_data_in''
          unfolding mv_idx_oldest' since_hist''_eq[symmetric] hist_sat'_eq
          by auto
        then have "x \<in> hist_sat_mv move init_tuple"
          using mv_data_in'' hd_props(1) dbs_props
          unfolding hist_sat_mv_def
          by (auto split: list.splits)
      }
      ultimately show ?thesis by auto
    qed
    moreover have "since_sat_mv move init_tuple = since_sat''"
    proof -
      have "(snd o snd o snd) (fold fold_op_f move init_tuple) = since_sat'"
        unfolding init_tuple_def
        by (simp flip: fold_tuple_res)
      then show ?thesis
        unfolding since_sat''_def since_sat_mv_def mv_idx_oldest'[symmetric] mv_idx_mid'[symmetric]
        by simp
    qed
    moreover have "(lin_data_in''_aux_mv move) = (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist))"
    proof -

      have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t))) = (\<lambda>(t, _). mem (args_ivl args) (mt - t))"
        using nt_mono(1) time not_memL_nt_mt
        by blast

      have filter_simp': "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t, _). mem (args_ivl args) (nt - t))"
        by auto

      have "(lin_data_in''_aux_mv move) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist) @ filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
        using auxlist_eqs(2) filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))"]
        unfolding lin_data_in''_aux_mv_def data_in'_aux_def move_filter
        by auto
      moreover have "(auxlist_data_in args mt auxlist) = filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)"
        unfolding auxlist_data_in_def
        using filter_filter[of "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(\<lambda>(t, _). mem (args_ivl args) (mt - t))" auxlist]
        by (auto simp add: filter_simp)
      moreover have "auxlist_data_prev args mt auxlist = linearize data_prev"
        using assms(1)
        unfolding valid_nmtaux_def prod.case by blast
      ultimately have "(lin_data_in''_aux_mv move) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist @ auxlist_data_prev args mt auxlist))"
        by auto
      then have "(lin_data_in''_aux_mv move) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) auxlist)"
        using auxlist_eqs
        by auto
      then have "(lin_data_in''_aux_mv move) = (auxlist_data_in args nt auxlist)"
        using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" auxlist]
        unfolding auxlist_data_in_def
        by (auto simp add: filter_simp')
      then show ?thesis using data_in_auxlist_filter_eq by auto
    qed
    ultimately have "(case Mapping.lookup (tuple_since_hist'') as of
      None \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)"
       "(as \<in> hist_sat'') = (linearize data_in'' \<noteq> [] \<and> (\<forall>(t, r)\<in>set (linearize data_in''). as \<in> r))"
       "(as \<in> since_sat'' \<longrightarrow> as \<in> hist_sat'' \<or> tuple_since_lhs as (linearize data_in'') args (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)))"
       "(tuple_since_lhs as (linearize data_in'') args (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) \<longrightarrow> as \<in> since_sat'')"
      by (auto simp add: mv_data_in''[symmetric] mv_idx_oldest'[symmetric] mv_idx_mid'[symmetric] split: option.splits)
  }
  then have fold_induct_props: "\<forall>as. (case Mapping.lookup (tuple_since_hist'') as of
      None \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)"
       "\<forall>as. (as \<in> hist_sat'') = (linearize data_in'' \<noteq> [] \<and> (\<forall>(t, r)\<in>set (linearize data_in''). as \<in> r))"
       "\<forall>as. (as \<in> since_sat'' \<longrightarrow> as \<in> hist_sat'' \<or> tuple_since_lhs as (linearize data_in'') args (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)))"
       "\<forall>as. (tuple_since_lhs as (linearize data_in'') args (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) \<longrightarrow> as \<in> since_sat'')"
    by auto

  show tuple_since_hist''_props: "\<forall>as. (case Mapping.lookup (tuple_since_hist'') as of
      None \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)"
    using fold_induct_props(1)
    by auto
  
  have "\<forall>as \<in> Mapping.keys (tuple_since_hist''). wf_tuple (args_R args) as"
  proof -
    {
      fix as
      assume "as \<in> Mapping.keys (tuple_since_hist'')"
      then obtain idx where "Mapping.lookup tuple_since_hist'' as = Some idx"
        by (meson Mapping.in_keysD)
      then have idx_props:
        "linearize data_in'' \<noteq> []"
        "idx < idx_mid'"
        "\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in'')). as \<in> y"
        using tuple_since_hist''_props
        unfolding tuple_since_tp_def
        by (auto split: option.splits)
      then have "idx - idx_oldest' < length (linearize data_in'')"
        using data_in''_len'
        by (metis add.commute add_diff_cancel_left' diff_is_0_eq diff_less_mono not_le_imp_less length_0_conv less_imp_le_nat)
      then have "last (linearize data_in'') \<in> set (drop (idx - idx_oldest') (linearize data_in''))"
        using idx_props(1)
        by (metis drop_eq_Nil last_drop last_in_set leD)
      then have as_in: "as \<in> snd (last (linearize data_in''))"
        using idx_props(3)
        by auto
      then obtain t r where t_r_def: "(t, r) = last (linearize data_in'')"
        using prod.collapse
        by blast
      then have "(t, r) \<in> set (linearize data_in'')"
        by (metis idx_props(1) last_in_set)
      then have "\<exists>l. (t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist))"
        unfolding auxlist_data_in[symmetric] by (simp add: image_iff Bex_def)
      then obtain l where "(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist))"
        by blast
      then have "(t, l, r) \<in> set auxlist"
        unfolding auxlist_data_in_def
        by auto
      moreover have "(\<forall>(t, relL, relR) \<in> set auxlist. table (args_L args) relL \<and> table (args_R args) relR)"
        using assms(1)
        unfolding valid_nmtaux_def prod.case by (elim conjE) assumption
      ultimately have "table (args_R args) r" by auto
      then have "wf_tuple (args_R args) as"
        using as_in t_r_def
        unfolding table_def
        by (metis snd_conv)
    }
    then show ?thesis by auto
  qed
  then show "table (args_R args) (Mapping.keys tuple_since_hist'')"
    unfolding table_def
    by auto

  
  show "(\<forall>tuple. tuple \<in> hist_sat'' \<longleftrightarrow>
      (\<not>Queue.is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r
    ))"
  proof -
    {
      fix tuple
      have "tuple \<in> hist_sat'' \<longleftrightarrow>
      (\<not>Queue.is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r)"
      proof (rule iffI)
        assume "tuple \<in> hist_sat''"
        then have props:
          "(\<not>Queue.is_empty data_in'')"
          "\<forall>(t, r)\<in>set (linearize data_in''). tuple \<in> r"
          using fold_induct_props(2) Queue.is_empty_alt
          by auto
        {
          fix t l r
          assume "(t, l, r) \<in> set (auxlist_data_in args nt auxlist)"
          then have "(t, r) \<in> set (linearize data_in'')"
            unfolding auxlist_data_in[symmetric] data_in_auxlist_filter_eq
            using set_map[of "(\<lambda>(t, l, y). (t, y))" "auxlist_data_in args nt auxlist"]
            by force
          then have "tuple \<in> r"
            using props(2)
            by auto
        }
        then show "(\<not>Queue.is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r)"
          using data_in_auxlist_filter_eq props(1)
          by auto
      next
        assume assm: "(\<not>Queue.is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r)"
        then have "\<forall>(t, r) \<in> set (linearize data_in''). tuple \<in> r"
          using auxlist_data_in data_in_auxlist_filter_eq[symmetric] set_map[of "(\<lambda>(t, l, y). (t, y))" "auxlist_data_in args nt auxlist"]
          by auto
        then show "tuple \<in> hist_sat''"
          using assm fold_induct_props(2) Queue.is_empty_alt
          by auto
      qed
    }
    then show ?thesis by auto
  qed

  show "(\<forall>tuple. tuple \<in> since_sat'' \<longrightarrow>
      ((tuple \<in> hist_sat'') \<or> tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)))
    )"
    using fold_induct_props(3)
    by auto

  show "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)) \<longrightarrow>
      tuple \<in> since_sat''
    )"
    using fold_induct_props(4)
    by auto
  
qed

lemma valid_update_nmtaux':
  assumes valid_before: "valid_nmtaux args cur
    (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes nt_mono: "nt \<ge> cur"
  assumes "(idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys', tuple_since_hist'', hist_sat'', since_sat'') = update_nmtaux' args nt idx_mid idx_oldest data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat"
  shows "valid_nmtaux args nt
    (nt, idx_next, idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys', tuple_since_hist'', hist_sat'', since_sat'') (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  define auxlist' where "auxlist' = filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist"
  have "(if mem (args_ivl args) 0 then set (args_L args) \<subseteq> set (args_R args) else (args_L args) = (args_R args))"
    using assms(1)
    unfolding valid_nmtaux_def prod.case by blast
  moreover have "\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args"
    using assms(1)
    unfolding valid_nmtaux_def prod.case by blast
  moreover have "distinct (args_L args)"
    using assms(1)
    unfolding valid_nmtaux_def prod.case by blast
  moreover have "distinct (args_R args)"
    using assms(1)
    unfolding valid_nmtaux_def prod.case by blast
  moreover have "(\<forall>(t, relL, relR) \<in> set auxlist'. table (args_L args) relL \<and> table (args_R args) relR)"
    using assms(1)
    unfolding auxlist'_def
    by (simp add: valid_nmtaux_def)
  moreover have "table (args_L args) (Mapping.keys tuple_in_once')"
    by (rule valid_update_nmtaux'_unfolded(1)[OF assms])
  moreover have "table (args_R args) (Mapping.keys tuple_since_hist'')"
    by (rule valid_update_nmtaux'_unfolded(2)[OF assms])
  moreover have "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_L args) as)"
    by (rule valid_update_nmtaux'_unfolded(3)[OF assms])
  moreover have "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_R args) as)"
    by (rule valid_update_nmtaux'_unfolded(4)[OF assms])
  moreover have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in''))). wf_tuple (args_R args) as)"
    by (rule valid_update_nmtaux'_unfolded(10)[OF assms])
  moreover have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist')) =
    ts_tuple_rel (set (linearize data_in''))"
    unfolding auxlist'_def
    by (rule valid_update_nmtaux'_unfolded(11)[OF assms])
  moreover have "sorted (map fst auxlist')"
    using assms(1) sorted_filter
    unfolding auxlist'_def
    by (auto simp add: valid_nmtaux_def)
  moreover have "auxlist_data_prev args nt auxlist' = (linearize data_prev')"
    unfolding auxlist'_def
    by (rule valid_update_nmtaux'_unfolded(5)[OF assms])
  moreover have "auxlist_data_prev args nt auxlist' = drop (length (linearize data_in'')) auxlist'"
    unfolding auxlist'_def
    by (rule valid_update_nmtaux'_unfolded(9)[OF assms])
  moreover have "length (linearize data_prev') + idx_mid' = idx_next"
    by (rule valid_update_nmtaux'_unfolded(8)[OF assms])
  moreover have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in'')"
    unfolding auxlist'_def
    by (rule valid_update_nmtaux'_unfolded(12)[OF assms])
  moreover have "auxlist_data_in args nt auxlist' = take (length (linearize data_in'')) auxlist'"
    unfolding auxlist'_def
    by (rule valid_update_nmtaux'_unfolded(13)[OF assms])
  moreover have "length (linearize data_in'') + idx_oldest' = idx_mid'"
    by (rule valid_update_nmtaux'_unfolded(14)[OF assms])
  moreover have "(\<forall>db \<in> set auxlist'. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
  proof -
    {
      fix db
      assume assm: "db \<in> set auxlist'"

      have "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db))"
        using assms(1)
        unfolding valid_nmtaux_def prod.case by blast
      moreover have "db \<in> set auxlist"
        using assm
        unfolding auxlist'_def
        by auto
      ultimately have "time db \<le> mt"
        by auto
      then have "time db \<le> nt"
        using nt_mono assms(1)
        by (simp add: valid_nmtaux_def)

      moreover have "memR (args_ivl args) (nt - time db)"
        using assm
        unfolding auxlist'_def time_def
        by auto

      ultimately have "time db \<le> nt \<and> memR (args_ivl args) (nt - time db)"
        by auto
    }
    then show ?thesis by auto
  qed
  moreover have "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
    by (rule valid_update_nmtaux'_unfolded(6)[OF assms])
  moreover have "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l as) \<and>
    (\<forall>as. (case Mapping.lookup tuple_since_hist'' as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)
    )"
    using valid_update_nmtaux'_unfolded(7,15)[OF assms]
    by (rule conjI)
  moreover have "(\<forall>tuple. tuple \<in> hist_sat'' \<longleftrightarrow>
      (\<not>Queue.is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r
    ))"
    unfolding auxlist'_def
    by (rule valid_update_nmtaux'_unfolded(16)[OF assms])
  moreover have "(\<forall>tuple. tuple \<in> since_sat'' \<longrightarrow>
      ((tuple \<in> hist_sat'') \<or> tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt auxlist'))
    )"
    unfolding auxlist'_def
    by (rule valid_update_nmtaux'_unfolded(17)[OF assms])
  moreover have "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt auxlist') \<longrightarrow>
      tuple \<in> since_sat''
    )"
    unfolding auxlist'_def
    by (rule valid_update_nmtaux'_unfolded(18)[OF assms])
  moreover have "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
    by (rule valid_update_nmtaux'_unfolded(19)[OF assms])
  ultimately show ?thesis
    unfolding auxlist'_def valid_nmtaux_def prod.case
    by (elim conjE) (intro conjI refl)
qed

lemma valid_update_nmtaux_unfolded:
  assumes "nt \<ge> cur"
  assumes "table (args_L args) l"
  assumes "table (args_R args) r"
  assumes "valid_nmtaux args cur (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
    shows "valid_nmtaux
      args
      nt
      (update_nmtaux args nt l r (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat))
      ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])
  "
proof -
  define update_nmtaux'_res
    where "update_nmtaux'_res = update_nmtaux' args nt idx_mid idx_oldest data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat"

  define idx_mid' where "idx_mid' = fst update_nmtaux'_res"
  define idx_oldest' where "idx_oldest' = (fst o snd) update_nmtaux'_res"
  define data_prev' where "data_prev' = (fst o snd o snd) update_nmtaux'_res"
  define data_in' where "data_in' = (fst o snd o snd o snd) update_nmtaux'_res"
  define tuple_in_once' where "tuple_in_once' = (fst o snd o snd o snd o snd) update_nmtaux'_res"
  define tuple_in_once_keys' where "tuple_in_once_keys' = (fst o snd o snd o snd o snd o snd) update_nmtaux'_res"
  define tuple_since_hist' where "tuple_since_hist'     = (fst o snd o snd o snd o snd o snd o snd) update_nmtaux'_res"
  define hist_sat' where "hist_sat'                     = (fst o snd o snd o snd o snd o snd o snd o snd) update_nmtaux'_res"
  define since_sat' where "since_sat'                   = (snd o snd o snd o snd o snd o snd o snd o snd) update_nmtaux'_res"

  define auxlist' where "auxlist' = filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist"

  have update_eq: "(idx_mid', idx_oldest', data_prev', data_in', tuple_in_once', tuple_in_once_keys', tuple_since_hist', hist_sat', since_sat') =
    update_nmtaux' args nt idx_mid idx_oldest data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat"
    using update_nmtaux'_res_def
    unfolding idx_mid'_def idx_oldest'_def data_prev'_def data_in'_def tuple_in_once'_def tuple_in_once_keys'_def tuple_since_hist'_def hist_sat'_def since_sat'_def
    by auto

  have valid: "valid_nmtaux args nt (nt, idx_next, idx_mid', idx_oldest', data_prev', data_in', tuple_in_once', tuple_in_once_keys', tuple_since_hist', hist_sat', since_sat')
     auxlist'"
    unfolding auxlist'_def
    using valid_update_nmtaux'[OF assms(4) assms(1) update_eq] .

  define update_nmtaux_res where "update_nmtaux_res = update_nmtaux args nt l r (cur, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)"
  define auxlist'' where "auxlist'' = auxlist' @ [(nt, l, r)]"

  have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
    using valid
    unfolding valid_nmtaux_def prod.case by blast
  then have data_in'_len_leq: "length (linearize data_in') \<le> length auxlist'"
    unfolding auxlist_data_in_def
    by (metis (no_types, lifting) length_filter_le length_map)

  have proj_l: "\<forall>as \<in> l. as = restrict (args_L args) (args_R args) as" if "\<not> mem (args_ivl args) 0"
  proof -
    have "args_L args = args_R args"
      using assms(4) that by (simp add: valid_nmtaux_def)
    then show ?thesis
      using assms(2) restrict_idle[OF valid_nmtaux_distinct(1)[OF assms(4)]]
      unfolding table_def
      by metis
  qed


  show ?thesis
  proof (cases "mem (args_ivl args) 0")    
    case True

    define idx_mid'' where "idx_mid'' = idx_mid'+1"
    define idx_next'' where "idx_next'' = idx_next+1"
    define data_in'' where "data_in'' = (append_queue (nt, r) data_in')"
    define tuple_since_hist'' where "tuple_since_hist'' = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist'"
    define tuple_since_hist''' where "tuple_since_hist''' = upd_set tuple_since_hist'' (\<lambda>_. idx_mid') (r - Mapping.keys tuple_since_hist'')"
    define hist_sat'' where "hist_sat'' = (if Queue.is_empty data_in' then r else hist_sat' \<inter> r)"
    define since_sat'' where "since_sat'' = (since_sat' \<inter> r) \<union> {as \<in> r. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as l}"

    have res_eq: "(
        nt,
        idx_next'',
        idx_mid'',
        idx_oldest',
        data_prev',
        data_in'',
        tuple_in_once',
        tuple_in_once_keys',
        tuple_since_hist''',
        hist_sat'',
        since_sat''
      ) = update_nmtaux args nt l r (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)"
      unfolding update_nmtaux_res_def idx_mid''_def idx_next''_def data_in''_def tuple_since_hist'''_def tuple_since_hist''_def hist_sat''_def since_sat''_def
      using True
      by (auto simp only: update_nmtaux_def Let_def update_eq[symmetric] split: if_splits)

    have auxlist_in_eq: "(auxlist_data_in args nt auxlist'') = (auxlist_data_in args nt auxlist') @ [(nt, l, r)]"
      using True
      unfolding auxlist_data_in_def auxlist''_def
      by auto

    have auxlist_prev_eq: "(auxlist_data_prev args nt auxlist'') = (auxlist_data_prev args nt auxlist')"
      using True
      unfolding auxlist_data_prev_def auxlist''_def
      by auto

    have "auxlist_data_prev args nt auxlist' = (linearize data_prev')"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have memL: "\<forall>t. memL (args_ivl args) t"
      using True
      by auto
    ultimately have lin_data_prev'_eq:
      "(linearize data_prev') = []"
      "auxlist_data_prev args nt auxlist' = []"
      unfolding auxlist_data_prev_def
      by auto
    moreover have "auxlist_data_prev args nt auxlist' = drop (length (linearize data_in')) auxlist'"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    ultimately have data_in'_len:"length (linearize data_in') = length auxlist'"
      using data_in'_len_leq
      by auto
    moreover have "auxlist_data_in args nt auxlist' = take (length (linearize data_in')) auxlist'"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    ultimately have auxlist_in_eq:
      "auxlist_data_in args nt auxlist' = auxlist'"
      "auxlist_data_in args nt auxlist'' = auxlist' @ [(nt, l, r)]"
      using auxlist_in_eq
      by auto

    have "(if mem (args_ivl args) 0 then set (args_L args) \<subseteq> set (args_R args) else (args_L args) = (args_R args))"
      using assms(4)
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args"
      using assms(4)
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "distinct (args_L args)"
      using assms(4)
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "distinct (args_R args)"
      using assms(4)
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "(\<forall>(t, relL, relR) \<in> set auxlist''. table (args_L args) relL \<and> table (args_R args) relR)"
    proof -
      have "(\<forall>(t, relL, relR) \<in> set auxlist'. table (args_L args) relL \<and> table (args_R args) relR)"
        using valid
        unfolding valid_nmtaux_def prod.case by (elim conjE) assumption
      then show ?thesis using assms(2-3) unfolding auxlist''_def by auto
    qed
    moreover have "table (args_L args) (Mapping.keys tuple_in_once')"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "table (args_R args) (Mapping.keys tuple_since_hist''')"
    proof -
      have "table (args_R args) (Mapping.keys tuple_since_hist')"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then have "table (args_R args) (Mapping.keys tuple_since_hist'')"
        unfolding tuple_since_hist''_def
        by (meson table_subset keys_filter)
      moreover have "table (args_R args) (r - Mapping.keys tuple_since_hist'')"
        using assms(3)
        unfolding table_def
        by (meson DiffD1)
      ultimately show ?thesis
        unfolding tuple_since_hist'''_def
        by (metis Mapping_upd_set_keys table_Un)
    qed
    moreover have "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_L args) as)"
      using valid
      unfolding valid_nmtaux_def prod.case by (elim conjE) assumption
    moreover have "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_R args) as)"
      using valid
      unfolding valid_nmtaux_def prod.case by (elim conjE) assumption
    moreover have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in''))). wf_tuple (args_R args) as)"
    proof -
      have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in'))). wf_tuple (args_R args) as)"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        using assms(3)
        unfolding data_in''_def append_queue_rep table_def
        by auto
    qed
    moreover have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist'')) =
      ts_tuple_rel (set (linearize data_in''))"
    proof -
      have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist')) =
      ts_tuple_rel (set (linearize data_in'))"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      moreover have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist'')) = ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist')) \<union> ts_tuple_rel_binary_rhs (set ([(nt, l, r)]))"
        using auxlist_in_eq
        unfolding ts_tuple_rel_f_def
        by auto
      moreover have "ts_tuple_rel (set (linearize data_in'')) = ts_tuple_rel (set (linearize data_in')) \<union> ts_tuple_rel (set [(nt, r)])"
        unfolding data_in''_def ts_tuple_rel_f_def append_queue_rep
        by auto
      ultimately show ?thesis
        unfolding ts_tuple_rel_f_def
        by auto
    qed
    moreover have "sorted (map fst auxlist'')"
    proof -
      have
        "sorted (map fst auxlist')"
        "\<forall>db \<in> set auxlist'. time db \<le> nt"
        using valid
        unfolding valid_nmtaux_def prod.case by blast+
      then show ?thesis
        unfolding auxlist''_def time_def
        using sorted_append[of "map fst auxlist'" "map fst [(nt, l, r)]"]
        by auto
    qed
    moreover have "auxlist_data_prev args nt auxlist'' = (linearize data_prev')"
      unfolding auxlist_prev_eq
      using valid
      by (simp add: valid_nmtaux_def)
    moreover have "auxlist_data_prev args nt auxlist'' = drop (length (linearize data_in'')) auxlist''"
      using True data_in'_len memL
      unfolding auxlist''_def data_in''_def append_queue_rep auxlist_data_prev_def
      by auto
    moreover have "length (linearize data_prev') + idx_mid'' = idx_next''"
      using valid
      unfolding idx_mid''_def idx_next''_def
      by (simp add: valid_nmtaux_def)
    moreover have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist'') = (linearize data_in'')"
    proof -
      have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
     then show ?thesis
      unfolding auxlist_in_eq data_in''_def append_queue_rep
      by auto
    qed
    moreover have "auxlist_data_in args nt auxlist'' = take (length (linearize data_in'')) auxlist''"
      unfolding auxlist_in_eq(2) data_in''_def append_queue_rep
      unfolding auxlist''_def
      using take_append[of "length auxlist'" auxlist' "[(nt, l, r)]"] length_append[of "linearize data_in'" "[(nt, r)]"]
      by (simp add: data_in'_len)
    moreover have data_in''_len: "length (linearize data_in'') + idx_oldest' = idx_mid''"
    proof -
      have "length (linearize data_in') + idx_oldest' = idx_mid'"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        unfolding idx_mid''_def data_in''_def append_queue_rep
        by auto
    qed
    moreover have "(\<forall>db \<in> set auxlist''. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
    proof -
      have "(\<forall>db \<in> set auxlist'. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        unfolding auxlist''_def time_def
        by auto
    qed
    moreover have "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l as)"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "(\<forall>as. (case Mapping.lookup tuple_since_hist''' as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx)
    )"
    proof -
      have before: "(\<forall>as. (case Mapping.lookup tuple_since_hist' as of
        Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx
        | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx)
      )"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      have non_empty: "linearize data_in'' \<noteq> []"
        unfolding data_in''_def append_queue_rep
        by auto
      have data_in''_last: "last (linearize data_in'') = (nt, r)"
        unfolding data_in''_def append_queue_rep
        by auto
      have before_len:
        "length (linearize data_in') + idx_oldest' = idx_mid'"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      {
        fix as
        have "(case Mapping.lookup tuple_since_hist''' as of
          Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx
          | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx)"
        proof (cases "Mapping.lookup tuple_since_hist''' as")
          case None
          then have
            "as \<notin> (r - Mapping.keys tuple_since_hist'')"
            unfolding tuple_since_hist'''_def
            by (metis Mapping_lookup_upd_set option.simps(3))
          moreover have hist'': "Mapping.lookup tuple_since_hist'' as = None"
            using None
            unfolding tuple_since_hist'''_def
            by (metis Mapping_lookup_upd_set option.simps(3))
          ultimately have not_relR: "as \<notin> r"
            by (simp add: keys_is_none_rep)
          
          {
            fix idx
            assume "idx < idx_mid''"
            then have "last (linearize data_in'') \<in> set (drop (idx - idx_oldest') (linearize data_in''))"
              using non_empty data_in''_len
              by (metis add.commute add_diff_inverse_nat add_less_cancel_left diff_is_0_eq dual_order.strict_iff_order last_drop last_in_set length_drop length_greater_0_conv zero_less_diff)
            moreover have "as \<notin> snd (last (linearize data_in''))"
            using not_relR data_in''_last
              by simp
            ultimately have "\<not>(\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in'')). as \<in> y)"
              by fastforce
          }
          then have "\<forall>idx. \<not> tuple_since_tp args as (linearize data_in'') (idx_oldest') (idx_mid'') idx"
            unfolding tuple_since_tp_def
            by auto

          then show ?thesis using None by auto
        next
          case (Some idx)
          then have "tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx"
          proof (cases "as \<in> (r - Mapping.keys tuple_since_hist'')")
            case True
            then have idx_eq: "idx = idx_mid'"
              using Some
              unfolding tuple_since_hist'''_def
              by (simp add: Mapping_lookup_upd_set)
            then have drop_eq: "drop (idx - idx_oldest') (linearize data_in'') = [(nt, r)]"
              using data_in''_len
              unfolding idx_mid''_def data_in''_def append_queue_rep
              by auto
            then have "\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in'')). as \<in> y"
              using True
              by auto
            moreover have "idx_oldest' < idx \<longrightarrow> as \<notin> snd (linearize data_in'' ! (idx - idx_oldest' - 1))"
            proof -
              {
                assume assm: "idx_oldest' < idx"
                then have before_non_empty: "linearize data_in' \<noteq> []"
                  using before_len idx_eq
                  by auto
                have "Mapping.lookup tuple_since_hist' as = None"
                  using True
                  unfolding tuple_since_hist''_def
                  by (metis DiffD1 DiffD2 Mapping_keys_intro Mapping_lookup_filter_Some)
                then have not_hist: "\<forall>idx. \<not> tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx"
                  using before
                  by (simp add: option.case_eq_if)

                have "as \<notin> snd (last (linearize data_in'))"
                  using no_hist_last_not_sat[OF before_len not_hist before_non_empty]
                  by auto
                then have "as \<notin> snd (linearize data_in'' ! (idx - idx_oldest' - 1))"
                  using data_in'_len idx_eq
                  unfolding data_in''_def
                  by (metis add_diff_cancel_right' append_eq_conv_conj append_queue_rep assm before_len before_non_empty diff_less last_conv_nth leI not_one_le_zero nth_take zero_less_diff)
              }
              then show ?thesis by auto
            qed
            ultimately have "tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx"
              using non_empty idx_eq
              unfolding tuple_since_tp_def idx_mid''_def
              by auto
            then show ?thesis
              by auto
          next
            case False
            then have "Mapping.lookup tuple_since_hist'' as = Some idx"
              using Some
              unfolding tuple_since_hist'''_def
              by (metis Mapping_lookup_upd_set)
            then have as_mem:
              "as \<in> r \<and> Mapping.lookup tuple_since_hist' as = Some idx"
              unfolding tuple_since_hist''_def
              by (metis Mapping_lookup_filter_None Mapping_lookup_filter_not_None option.simps(3))

            then have tuple_since: "tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx"
              using before
              by (auto split: option.splits)
            then have idx_props:
              "idx < idx_mid'"
              "\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in')). as \<in> y"
              "idx_oldest' < idx \<longrightarrow> as \<notin> snd (linearize data_in' ! (idx - idx_oldest' - 1))"
              unfolding tuple_since_tp_def
              by auto

            have "idx - idx_oldest' \<le> length (linearize data_in')"
              using before_len idx_props(1)
              by auto
            then have "\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in'')). as \<in> y"
              using idx_props(2) as_mem
              unfolding data_in''_def append_queue_rep
              by auto
            moreover have "linearize data_in'' ! (idx - idx_oldest' - 1) = linearize data_in' ! (idx - idx_oldest' - 1)"
              using before_len idx_props
              unfolding data_in''_def append_queue_rep
              by (metis (no_types, lifting) diff_is_0_eq idx_append not_le_imp_less length_greater_0_conv less_diff_conv2 less_imp_diff_less less_or_eq_imp_le tuple_since tuple_since_tp_def)

            ultimately have "tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx"
              using non_empty idx_props
              unfolding tuple_since_tp_def idx_mid''_def
              by auto
            then show ?thesis by auto
          qed
          then show ?thesis
            using Some
            by auto
        qed
      }
      
      then show ?thesis
        by auto
    qed
    moreover have "(\<forall>tuple. tuple \<in> hist_sat'' \<longleftrightarrow>
        (\<not>Queue.is_empty data_in'') \<and> (
          \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
      ))"
    proof -
      have before: "(\<forall>tuple. tuple \<in> hist_sat' \<longleftrightarrow>
        (\<not>Queue.is_empty data_in') \<and> (
          \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r
      ))"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      {
        fix tuple

        {
          assume assm: "Queue.is_empty data_in'"
          have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
            using valid
            unfolding valid_nmtaux_def prod.case by blast
          then have "(auxlist_data_in args nt auxlist') = []"
            using assm Queue.is_empty_alt[of data_in']
            by auto
          then have "auxlist_data_in args nt auxlist'' = [(nt, l, r)]"
            using auxlist_in_eq
            by auto
        }
        then have empty_data_in': "Queue.is_empty data_in' \<longrightarrow> auxlist_data_in args nt auxlist'' = [(nt, l, r)]"
          by auto

        have "tuple \<in> hist_sat'' \<longleftrightarrow>
          (\<not>Queue.is_empty data_in'') \<and> (
            \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
        )"
        proof (rule iffI)
          assume assm: "tuple \<in> hist_sat''"
          show "(\<not>Queue.is_empty data_in'') \<and> (
              \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
          )"
          proof (cases "Queue.is_empty data_in'")
            case True
            then have tuple_mem: "tuple \<in> r"
              using assm
              unfolding hist_sat''_def
              by auto
            
            then have "\<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r"
              using empty_data_in' True tuple_mem
              by auto
            moreover have "linearize data_in'' \<noteq> []"
              unfolding data_in''_def append_queue_rep
              by auto
            ultimately show ?thesis
              using Queue.is_empty_alt
              by auto
          next
            case False
            then have tuple_mem:
              "tuple \<in> hist_sat'"
              "tuple \<in> r"
              using assm
              unfolding hist_sat''_def
              by auto
            then have props: "(\<not>Queue.is_empty data_in') \<and> (
                \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r
            )"
              using before
              by auto
            then have all: "\<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r"
              using tuple_mem(2)
              unfolding auxlist_in_eq set_append
              by auto
  
            have "linearize data_in' \<noteq> []"
              using props Queue.is_empty_alt
              by auto
            then have "linearize data_in'' \<noteq> []"
              unfolding data_in''_def append_queue_rep
              by auto
            then show ?thesis
              using all Queue.is_empty_alt
              by auto
          qed
        next
          assume assm: "(\<not>Queue.is_empty data_in'') \<and> (
              \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
          )"
          then show "tuple \<in> hist_sat''"
          proof (cases "Queue.is_empty data_in'")
            case True
            then have "tuple \<in> r"
              using assm empty_data_in'
              by auto
            then show ?thesis
              unfolding hist_sat''_def
              using True
              by auto
          next
            case False
            then have tuple_mem:
              "tuple \<in> r"
              "\<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r"
              using assm auxlist_in_eq
              by auto
            then have "tuple \<in> hist_sat'"
              using before False
              by auto
            then show ?thesis
              unfolding hist_sat''_def
              using False tuple_mem(1)
              by auto
          qed
        qed
      }
      then show ?thesis by auto
    qed
    moreover have "(\<forall>tuple. tuple \<in> since_sat'' \<longrightarrow>
        ((tuple \<in> hist_sat'') \<or> tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt auxlist''))
      )"
    proof -
      have before: "(\<forall>tuple. tuple \<in> since_sat' \<longrightarrow>
          ((tuple \<in> hist_sat') \<or> tuple_since_lhs tuple (linearize data_in') args (auxlist_data_in args nt auxlist'))
        )"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      {
        fix tuple
        assume assm: "tuple \<in> since_sat''"
        have non_empty: "linearize data_in'' \<noteq> []"
          unfolding data_in''_def append_queue_rep
          by auto
        have "tuple \<in> (since_sat' \<inter> r) \<union> {as \<in> r. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as l}"
          using assm since_sat''_def
          by auto
        moreover {
          assume assm: "tuple \<in> (since_sat' \<inter> r)"
          then have "tuple \<in> hist_sat' \<or> tuple_since_lhs tuple (linearize data_in') args (auxlist_data_in args nt auxlist')"
            using before
            by auto
          moreover {
            assume hist: "tuple \<in> hist_sat'"
            moreover have "(\<forall>tuple. tuple \<in> hist_sat' \<longleftrightarrow>
              (\<not>Queue.is_empty data_in') \<and> (
                \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r
            ))"
              using valid
              unfolding valid_nmtaux_def prod.case by blast
            ultimately have "(\<not>Queue.is_empty data_in')"
              by auto
            then have "tuple \<in> hist_sat''"
              using assm hist
              unfolding hist_sat''_def
              by auto
          }
          moreover {
            assume since: "tuple_since_lhs tuple (linearize data_in') args (auxlist_data_in args nt auxlist')"
            then have "linearize data_in' \<noteq> []"
              unfolding tuple_since_lhs_def
              by auto
            obtain n where n_props:
              "n\<in>{0..<length (linearize data_in')}"
              "let suffix = drop n (auxlist_data_in args nt auxlist') in (\<forall>(t, l, y)\<in>set suffix. tuple \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)"
              using since
              unfolding tuple_since_lhs_def
              by auto
            
            have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
              using valid
              unfolding valid_nmtaux_def prod.case by blast
            then have len_eq: "length (auxlist_data_in args nt auxlist') = length (linearize data_in')"
              using length_map
              by metis
            then have n_le: "n < length (auxlist_data_in args nt auxlist')"
              using n_props(1)
              by auto
            moreover have "(auxlist_data_in args nt auxlist'') = (auxlist_data_in args nt auxlist') @ [(nt, l, r)]"
              using auxlist_in_eq
              by auto
            ultimately have drop_eq: "drop n (auxlist_data_in args nt auxlist'') = drop n (auxlist_data_in args nt auxlist') @ [(nt, l, r)]"
              by auto

            have "let suffix = drop n (auxlist_data_in args nt auxlist'') in (\<forall>(t, l, y)\<in>set suffix. tuple \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)"
              using n_props(2) n_le len_eq assm
              unfolding drop_eq Let_def
              by auto
            moreover have "n\<in>{0..<length (linearize data_in'')}"
              using n_props(1)
              unfolding data_in''_def append_queue_rep
              by auto
            ultimately have "tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt auxlist'')"
              using non_empty
              unfolding tuple_since_lhs_def
              by blast
          }
          ultimately have "tuple \<in> hist_sat'' \<or> tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt auxlist'')"
            by auto
        }
        moreover {
          define n where "n = length (auxlist_data_in args nt auxlist'') - 1"
          assume "tuple \<in> {as \<in> r. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as l}"
          then have tuple_props: "tuple \<in> r" "proj_tuple_in_join (args_pos args) (args_L args) (args_R args) tuple l"
            by auto
          have drop_eq: "drop n (auxlist_data_in args nt auxlist'') = [(nt, l, r)]"
            unfolding n_def
            using auxlist_in_eq
            by auto
          have "\<forall>(t, l, y)\<in>set (drop n (auxlist_data_in args nt auxlist'')). tuple \<in> y"
            using drop_eq tuple_props
            by auto
          moreover have "join_cond (args_pos args) (relL (hd (drop n (auxlist_data_in args nt auxlist'')))) (restrict (args_L args) (args_R args) tuple)"
            using tuple_props
            unfolding drop_eq relL_def
            by (simp add: proj_tuple_in_join_def)
          moreover have "n\<in>{0..<length (linearize data_in'')}"
          proof -
            have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
              using valid
              unfolding valid_nmtaux_def prod.case by blast
            then show ?thesis
              using auxlist_in_eq length_map[of "(\<lambda>(t, l, r). (t, r))" "(auxlist_data_in args nt auxlist')"]
              unfolding data_in''_def append_queue_rep n_def
              by auto
          qed
          ultimately have "tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt auxlist'')"
            using non_empty
            unfolding tuple_since_lhs_def
            by (auto simp add: Let_def)
        }
        ultimately have "tuple \<in> hist_sat'' \<or> tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt auxlist'')"
          by auto
      }
      then show ?thesis by auto
    qed
    moreover have "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt auxlist'') \<longrightarrow>
        tuple \<in> since_sat''
      )"
    proof -
      have before: "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in') args (auxlist_data_in args nt auxlist') \<longrightarrow>
        tuple \<in> since_sat'
      )"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      {
        fix tuple
        assume assm: "tuple_since_lhs tuple (linearize data_in'') args (auxlist_data_in args nt auxlist'')"
        then have non_empty: "linearize data_in'' \<noteq> []"
          unfolding tuple_since_lhs_def
          by auto
        obtain n where n_props:
          "n\<in>{0..<length (linearize data_in'')}"
          "let suffix = drop n (auxlist_data_in args nt auxlist'') in (\<forall>(t, l, y)\<in>set suffix. tuple \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)"
          using assm
          unfolding tuple_since_lhs_def
          by auto
        {
          assume n_l: "n\<in>{0..<length (linearize data_in')}"
          then have "length (drop n auxlist') > 0"
            using data_in'_len
            by auto
          
          moreover have "set (drop n (auxlist_data_in args nt auxlist')) \<subseteq> set (drop n (auxlist_data_in args nt auxlist''))"
            using auxlist_in_eq Let_def
            by (auto simp add: data_in'_len)
          ultimately have "let suffix = drop n (auxlist_data_in args nt auxlist') in (\<forall>(t, l, y)\<in>set suffix. tuple \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (restrict (args_L args) (args_R args) tuple)"
            using n_props(2) n_l
            unfolding auxlist_in_eq Let_def
            by auto
          
          moreover have "linearize data_in' \<noteq> []"
            using n_l
            by auto
          ultimately have "tuple \<in> since_sat'"
            using n_l before
            unfolding tuple_since_lhs_def
            by blast
          moreover have "tuple \<in> r"
          proof -
            have "(nt, l, r) \<in> set (drop n (auxlist_data_in args nt auxlist''))"
              using n_l data_in'_len
              unfolding auxlist_in_eq(2)
              by simp
            then show ?thesis
              using n_props(2)
              unfolding Let_def
              by blast
          qed
          ultimately have "tuple \<in> since_sat' \<inter> r"
            by auto
        }
        moreover {
          assume "n \<notin> {0..<length (linearize data_in')}"
          then have "n = length (linearize data_in')"
            using n_props
            unfolding data_in''_def append_queue_rep
            by auto
          moreover have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
            using valid
            unfolding valid_nmtaux_def prod.case by blast
          ultimately have "drop n (auxlist_data_in args nt auxlist'') = [(nt, l, r)]"
            using auxlist_in_eq length_map[of "(\<lambda>(t, l, r). (t, r))" "(auxlist_data_in args nt auxlist')"]
            by auto
          then have "tuple \<in> r" "join_cond (args_pos args) l (restrict (args_L args) (args_R args) tuple)"
            using n_props(2)
            unfolding relL_def
            by (auto simp add: Let_def)
          then have "tuple \<in> {as \<in> r. proj_tuple_in_join (args_pos args) (args_L args) (args_R args) as l}"
            unfolding proj_tuple_in_join_def
            by auto
        }
        ultimately have "tuple \<in> since_sat''"
          unfolding since_sat''_def
          by auto
      }
      then show ?thesis by auto
    qed
    moreover have "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "time (nt, l, r) \<le> nt"
      unfolding time_def
      by auto
    ultimately show ?thesis
      unfolding res_eq[symmetric] auxlist''_def auxlist'_def valid_nmtaux_def prod.case
      by (intro conjI refl)
  next
    case False
    define data_prev'' where "data_prev'' = (append_queue (nt, l, r) data_prev')"
    define idx_next'' where "idx_next'' = idx_next+1"
    define tuple_in_once'' where "tuple_in_once'' = upd_set tuple_in_once' (\<lambda>_. nt) l"
    define tuple_in_once_keys'' where "tuple_in_once_keys'' = tuple_in_once_keys' \<union> l"

    have auxlist_in_eq: "(auxlist_data_in args nt auxlist'') = (auxlist_data_in args nt auxlist')"
      using False
      unfolding auxlist_data_in_def auxlist''_def
      by auto

    have auxlist_prev_eq: "(auxlist_data_prev args nt auxlist'') = (auxlist_data_prev args nt auxlist') @ [(nt, l, r)]"
      using False
      unfolding auxlist_data_prev_def auxlist''_def
      by auto

    have res_eq: "(
        nt,
        idx_next'',
        idx_mid',
        idx_oldest',
        data_prev'',
        data_in',
        tuple_in_once'',
        tuple_in_once_keys'',
        tuple_since_hist',
        hist_sat',
        since_sat'
      ) = update_nmtaux args nt l r (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)"
      unfolding update_nmtaux_res_def data_prev''_def idx_next''_def tuple_in_once''_def tuple_in_once_keys''_def
      using False
      by (auto simp only: update_nmtaux_def Let_def update_eq[symmetric] split: if_splits)
  
    have "(if mem (args_ivl args) 0 then set (args_L args) \<subseteq> set (args_R args) else (args_L args) = (args_R args))"
      using assms(4)
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args"
      using assms(4)
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "distinct (args_L args)"
      using assms(4)
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "distinct (args_R args)"
      using assms(4)
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "(\<forall>(t, relL, relR) \<in> set auxlist''. table (args_L args) relL \<and> table (args_R args) relR)"
    proof -
      have "(\<forall>(t, relL, relR) \<in> set auxlist'. table (args_L args) relL \<and> table (args_R args) relR)"
        using valid
        unfolding valid_nmtaux_def prod.case by (elim conjE) assumption
      then show ?thesis using assms(2-3) unfolding auxlist''_def by auto
    qed
    moreover have table_in_once'': "table (args_L args) (Mapping.keys tuple_in_once'')"
    proof -
      have "table (args_L args) (Mapping.keys tuple_in_once')"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        unfolding tuple_in_once''_def
        using assms(2)
        by (simp add: Mapping_upd_set_keys)
    qed
    moreover have "table (args_R args) (Mapping.keys tuple_since_hist')"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have data_prev''_relL: "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev''))). wf_tuple (args_L args) as)"
    proof -
      have "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_L args) as)"
        using valid
        unfolding valid_nmtaux_def prod.case by (elim conjE) assumption
      then show ?thesis
        using assms(2)
        unfolding data_prev''_def append_queue_rep relL_def table_def
        by auto
    qed
    moreover have "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev''))). wf_tuple (args_R args) as)"
    proof -
      have "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_R args) as)"
        using valid
        unfolding valid_nmtaux_def prod.case by (elim conjE) assumption
      then show ?thesis
        using assms(3)
        unfolding data_prev''_def append_queue_rep relR_def table_def
        by auto
    qed
    moreover have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in'))). wf_tuple (args_R args) as)"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist'')) =
      ts_tuple_rel (set (linearize data_in'))"
      unfolding auxlist_in_eq
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "sorted (map fst auxlist'')"
    proof -
      have
        "sorted (map fst auxlist')"
        "\<forall>db \<in> set auxlist'. time db \<le> nt"
        using valid
        unfolding valid_nmtaux_def prod.case by blast+
      then show ?thesis
        unfolding auxlist''_def time_def
        using sorted_append[of "map fst auxlist'" "map fst [(nt, l, r)]"]
        by auto
    qed
    moreover have data_prev''_auxlist: "auxlist_data_prev args nt auxlist'' = (linearize data_prev'')"
    proof -
      have "auxlist_data_prev args nt auxlist' = (linearize data_prev')"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        using False
        unfolding auxlist_data_prev_def auxlist''_def data_prev''_def append_queue_rep
        by auto
    qed
    moreover have "auxlist_data_prev args nt auxlist'' = drop (length (linearize data_in')) auxlist''"
    proof - 
      have "auxlist_data_prev args nt auxlist' = drop (length (linearize data_in')) auxlist'"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        using False data_in'_len_leq
        unfolding auxlist''_def auxlist_data_prev_def
        by auto
    qed
    moreover have "length (linearize data_prev'') + idx_mid' = idx_next''"
    proof -
      have "length (linearize data_prev') + idx_mid' = idx_next"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        unfolding data_prev''_def idx_next''_def append_queue_rep
        by auto
    qed
    moreover have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist'') = (linearize data_in')"
      unfolding auxlist_in_eq
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "auxlist_data_in args nt auxlist'' = take (length (linearize data_in')) auxlist''"
    proof -
      have "auxlist_data_in args nt auxlist' = take (length (linearize data_in')) auxlist'"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        using data_in'_len_leq False
        unfolding auxlist''_def auxlist_data_in_def
        by auto
    qed
    moreover have "length (linearize data_in') + idx_oldest' = idx_mid'"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "(\<forall>db \<in> set auxlist''. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
    proof -
      have "(\<forall>db \<in> set auxlist'. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        unfolding auxlist''_def time_def
        by auto
    qed
    moreover have "newest_tuple_in_mapping fst data_prev'' tuple_in_once'' (\<lambda>x. True)"
    proof -
      have before: "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      {
        fix tuple::"'a list"
        assume wf: "wf_tuple (args_L args) tuple"

        have ts_rel_union: "ts_tuple_rel_binary_lhs (set (linearize data_prev'')) = ts_tuple_rel_binary_lhs (set (linearize data_prev')) \<union> ts_tuple_rel_binary_lhs (set [(nt, l, r)])"
          unfolding ts_tuple_rel_f_def data_prev''_def append_queue_rep
          by auto

        have tuple_not_mem_empty: "tuple \<notin> l \<longrightarrow> {tas \<in> ts_tuple_rel_binary_lhs (set [(nt, l, r)]). tuple = snd tas} = {}"
          proof -
            {
              assume tuple_not_mem: "tuple \<notin> l"
              assume "{tas \<in> ts_tuple_rel_binary_lhs (set [(nt, l, r)]). True \<and> tuple = snd tas} \<noteq> {}"
              then obtain t as where as_props: "(t, as) \<in> ts_tuple_rel_binary_lhs (set [(nt, l, r)])" "tuple = as"
                by auto
              then have as_eq: "tuple = as"
                by auto
              obtain l' r' where "as \<in> l'" "(t, l', r') \<in> set [(nt, l, r)]"
                using as_props 
                unfolding ts_tuple_rel_f_def
                by auto
              then have "as \<in> l"
                by auto
              then have "False"
                using as_eq tuple_not_mem
                by auto
            }
            then show ?thesis by auto
          qed

        have "Mapping.lookup tuple_in_once'' tuple = safe_max (fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas})"
        proof (cases "Mapping.lookup tuple_in_once'' tuple")
          case None
          have tuple_not_mem: "tuple \<notin> l"
            using None
            unfolding tuple_in_once''_def
            by (metis Mapping_lookup_upd_set option.distinct(1))
          have "Mapping.lookup tuple_in_once' tuple = None"
            using None
            unfolding tuple_in_once''_def
            by (metis Mapping_lookup_upd_set option.distinct(1))
          then have "safe_max (fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). tuple = snd tas}) = None"
            using before
            unfolding newest_tuple_in_mapping_def
            by simp
          then have "{tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). tuple = snd tas} = {}"
            by (simp add: safe_max_empty)
          then have "\<forall>tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). tuple \<noteq> snd tas" 
            by blast
          then have "fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} = {}"
            using tuple_not_mem tuple_not_mem_empty
            unfolding data_prev''_def append_queue_rep ts_tuple_rel_f_def
            by auto
          then show ?thesis
            using None
            unfolding safe_max_def
            by (auto split: if_splits)
        next
          case (Some t)
          then show ?thesis
          proof (cases "tuple \<in> l")
            case True
            then have t_eq: "t = nt"
              using Some
              unfolding tuple_in_once''_def
              by (simp add: Mapping_lookup_upd_set)
            have "(nt, tuple) \<in> ts_tuple_rel_binary_lhs (set [(nt, l, r)])"
              using True
              unfolding ts_tuple_rel_f_def
              by auto
            then have "(nt, tuple) \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev''))"
              using ts_rel_union
              by auto
            then have nt_mem: "nt \<in> fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas}"
              using True
              by (metis (mono_tags) fst_conv imageI mem_Collect_eq snd_conv)

            then have non_empty: "fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} \<noteq> {}"
              by auto

            have "\<forall>t \<in> fst ` ts_tuple_rel_binary_lhs (set [(nt, l, r)]). t \<le> nt"
              unfolding ts_tuple_rel_f_def
              by auto
            moreover have "\<forall>t \<in> fst ` ts_tuple_rel_binary_lhs (set (linearize data_prev')). t \<le> nt"
            proof -
              have
                "(\<forall>db \<in> set auxlist'. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
                "auxlist_data_prev args nt auxlist' = (linearize data_prev')"
                using valid
                unfolding valid_nmtaux_def prod.case by blast+
              then have "\<forall>db \<in> set (linearize data_prev'). time db \<le> nt"
                unfolding auxlist_data_prev_def
                by (metis (no_types, lifting) mem_Collect_eq set_filter)
              then show ?thesis
                unfolding time_def ts_tuple_rel_f_def
                by auto
            qed
            ultimately have "\<forall>t \<in> fst ` ts_tuple_rel_binary_lhs (set (linearize data_prev'')). t \<le> nt"
              using ts_rel_union
              by auto
            then have "\<forall>t \<in> (fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas}). t \<le> nt"
              by auto
            then have "Max (fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas}) = nt"
              using nt_mem
              by (meson Max_eqI finite_nat_set_iff_bounded_le)
            then show ?thesis
              using Some t_eq non_empty
              unfolding safe_max_def
              by (auto split: if_splits)
          next
            case False
            then have "Mapping.lookup tuple_in_once'' tuple = Mapping.lookup tuple_in_once' tuple"
              using Some
              unfolding tuple_in_once''_def
              by (simp add: Mapping_lookup_upd_set)
            moreover have "fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} = fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). tuple = snd tas}"
              using False tuple_not_mem_empty ts_rel_union
              unfolding ts_tuple_rel_f_def
              by auto
            ultimately show ?thesis
              using before
              unfolding newest_tuple_in_mapping_def
              by auto
          qed
        qed
      }
      moreover {
        fix tuple::"'a list"
        assume wf: "\<not>wf_tuple (args_L args) tuple"

        then have lookup: "Mapping.lookup tuple_in_once'' tuple = None"
          using table_in_once''
          unfolding table_def
          by (meson Mapping_keys_intro)

        {
          assume "{tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} \<noteq> {}"
          then obtain t l r where "tuple \<in> l" "(t, l, r) \<in> set (linearize data_prev'')"
            unfolding ts_tuple_rel_f_def
            by auto
          then have "wf_tuple (args_L args) tuple"
            using data_prev''_relL
            unfolding relL_def
            by auto
          then have "False"
            using wf
            by auto
        }
        then have "{tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} = {}"
          by auto
        then have "Mapping.lookup tuple_in_once'' tuple = safe_max (fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas})"
          using lookup
          unfolding safe_max_def
          by auto
      }
      ultimately show ?thesis
        unfolding newest_tuple_in_mapping_def
        by auto
    qed
    moreover have "(\<forall>as \<in> Mapping.keys tuple_in_once''. case Mapping.lookup tuple_in_once'' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev'') \<and> join_cond (args_pos args) l as)"
    proof -
      have before: "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l as)"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      {
        fix as
        assume "as \<in> Mapping.keys tuple_in_once''"
        then obtain t where t_props: "Mapping.lookup tuple_in_once'' as = Some t"
          by (meson Mapping.in_keysD)
        have "case Mapping.lookup tuple_in_once'' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev'') \<and> join_cond (args_pos args) l as"
        proof (cases "as \<in> l")
          case True
          then have t_eq: "t = nt"
            using t_props
            unfolding tuple_in_once''_def
            by (simp add: Mapping_lookup_upd_set)
          have tlr: "(nt, l, r) \<in> set (linearize data_prev'')"
            unfolding data_prev''_def append_queue_rep
            by auto
          have pos: "args_pos args"
            using valid False
            unfolding valid_nmtaux_def prod.case by blast
          have "as \<in> l"
            using True
            by auto
          then have "join_cond (args_pos args) l as"
            using pos
            by auto
          then show ?thesis
            using t_props tlr pos t_eq
            by auto
        next
          case False
          then have "Mapping.lookup tuple_in_once'' as = Mapping.lookup tuple_in_once' as"
            unfolding tuple_in_once''_def
            by (simp add: Mapping_lookup_upd_set)
          then have lookup_t: "Mapping.lookup tuple_in_once' as = Some t"
            using t_props
            by simp
          then have "as \<in> Mapping.keys tuple_in_once'"
            by (simp add: Mapping_keys_intro)
          from lookup_t bspec[OF before this]
          have "\<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l as"
            by simp
          then show ?thesis
            using t_props
            unfolding data_prev''_def append_queue_rep
            by auto
        qed
      }
      then show ?thesis
        by auto
    qed
    moreover have "(\<forall>as. (case Mapping.lookup tuple_since_hist' as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx)
    )"
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "(\<forall>tuple. tuple \<in> hist_sat' \<longleftrightarrow>
        (\<not>Queue.is_empty data_in') \<and> (
          \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
      ))"
      unfolding auxlist_in_eq
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "(\<forall>tuple. tuple \<in> since_sat' \<longrightarrow>
        ((tuple \<in> hist_sat') \<or> tuple_since_lhs tuple (linearize data_in') args (auxlist_data_in args nt auxlist''))
      )"
    proof -
      have "(\<forall>tuple. tuple \<in> since_sat' \<longrightarrow>
        ((tuple \<in> hist_sat') \<or> tuple_since_lhs tuple (linearize data_in') args (auxlist_data_in args nt auxlist'))
      )"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        unfolding auxlist_in_eq
        by auto
    qed
    moreover have "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in') args (auxlist_data_in args nt auxlist'') \<longrightarrow>
        tuple \<in> since_sat'
      )"
      unfolding auxlist_in_eq
      using valid
      unfolding valid_nmtaux_def prod.case by blast
    moreover have "tuple_in_once_keys'' = Mapping.keys tuple_in_once''"
    proof -
      have "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
        using valid
        unfolding valid_nmtaux_def prod.case by blast
      then show ?thesis
        unfolding tuple_in_once_keys''_def tuple_in_once''_def
        by (simp add: Mapping_upd_set_keys)
    qed
    moreover have "time (nt, l, r) \<le> nt"
      unfolding time_def
      by auto
    ultimately show ?thesis
      unfolding res_eq[symmetric] auxlist''_def auxlist'_def valid_nmtaux_def prod.case
      by (intro conjI refl)
  qed
qed

lemma valid_update_nmtaux: "
    nt \<ge> cur \<Longrightarrow>
    table (args_L args) l \<Longrightarrow>
    table (args_R args) r \<Longrightarrow>
    valid_nmtaux args cur aux auxlist \<Longrightarrow>
    valid_nmtaux
      args
      nt
      (update_nmtaux args nt l r aux)
      ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])
  "
  using valid_update_nmtaux_unfolded
  by (cases aux) (fast)

lemma table_trigger_lhs: "table (args_L args) l \<Longrightarrow> table (args_L (trigger_args args)) (trigger_lhs args l)"
  by (auto simp: trigger_lhs_def table_def)

lemma join_cond_restrict_perm:
  assumes "set L = set R" "distinct L" "distinct R" "table L l" "wf_tuple R x"
  shows "join_cond pos (restrict R L ` l) x \<longleftrightarrow> join_cond pos l (restrict L R x)"
proof -
  have "x \<in> restrict R L ` l \<longleftrightarrow> restrict L R x \<in> l"
  proof
    assume "x \<in> restrict R L ` l"
    then obtain y where y: "y \<in> l" "x = restrict R L y"
      by auto
    then show "restrict L R x \<in> l"
      using restrict_restrict[of L R L y] restrict_idle[OF assms(2) tableD[OF assms(4) y(1)]] assms(1)
      by auto
  next
    assume "restrict L R x \<in> l"
    moreover have "restrict R L (restrict L R x) = x"
      using restrict_restrict[of R L R x] restrict_idle[OF assms(3,5)] assms(1)
      by auto
    ultimately show "x \<in> restrict R L ` l"
      by (metis image_eqI)
  qed
  then show ?thesis
    by auto
qed

lemma trigger_results_trigger_args:
  assumes "if mem (args_ivl args) 0 then set (args_L args) \<subseteq> set (args_R args) else set (args_L args) = set (args_R args)"
    "distinct (args_L args)" "distinct (args_R args)"
    "\<forall>(t, l, r) \<in> set auxlist. table (args_L args) l"
  shows "trigger_results (trigger_args args) cur (map (\<lambda>(t, l, r). (t, trigger_lhs args l, r)) auxlist) =
    trigger_results args cur auxlist"
proof (cases "mem (args_ivl args) 0 \<or> args_L args = args_R args")
  case True
  then have "trigger_args args = args"
    by (cases args) (auto simp: trigger_args_def)
  moreover have "map (\<lambda>(t, l, r). (t, trigger_lhs args l, r)) auxlist = auxlist"
    using True by (auto simp: trigger_lhs_def intro!: map_idI)
  ultimately show ?thesis
    by simp
next
  case False
  define f where "f = (\<lambda>(t :: ts, l :: event_data table, r :: event_data table). (t, restrict (args_R args) (args_L args) ` l, r))"
  have map_eq: "map (\<lambda>(t, l, r). (t, trigger_lhs args l, r)) auxlist = map f auxlist"
    using False by (auto simp: trigger_lhs_def f_def)
  have LR: "set (args_L args) = set (args_R args)"
    using assms(1) False by auto
  have len: "length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) (map f auxlist)) =
    length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist)"
    by (induction auxlist) (auto simp: f_def)
  have fst_nth: "fst (map f auxlist ! i) = fst (auxlist ! i)" "snd (snd (map f auxlist ! i)) = snd (snd (auxlist ! i))"
    if "i < length auxlist" for i
    using that by (auto simp: f_def split: prod.splits)
  have jc: "join_cond (args_pos args) ((fst \<circ> snd) (map f auxlist ! j)) (restrict (args_R args) (args_R args) x) \<longleftrightarrow>
    join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j)) (restrict (args_L args) (args_R args) x)"
    if "j < length auxlist" "wf_tuple (args_R args) x" for j x
  proof -
    obtain t l r where tlr: "auxlist ! j = (t, l, r)"
      by (cases "auxlist ! j") auto
    have tab: "table (args_L args) l"
      using assms(4) nth_mem[OF that(1)] tlr by fastforce
    have eq: "(fst \<circ> snd) (map f auxlist ! j) = restrict (args_R args) (args_L args) ` l"
      "(fst \<circ> snd) (auxlist ! j) = l"
      using that(1) tlr by (simp_all add: f_def)
    show ?thesis
      unfolding restrict_idle[OF assms(3) that(2)] eq
      by (rule join_cond_restrict_perm[OF LR assms(2,3) tab that(2)])
  qed
  have "{tuple. wf_tuple (args_R args) tuple \<and> (\<forall>i\<in>{0..<length (map f auxlist)}.
      let (t, l, r) = map f auxlist ! i in mem (args_ivl args) (cur - t) \<longrightarrow>
      tuple \<in> r \<or> (\<exists>j\<in>{i<..<length (map f auxlist)}.
        join_cond (args_pos args) ((fst \<circ> snd) (map f auxlist ! j)) (restrict (args_R args) (args_R args) tuple)))} =
    {tuple. wf_tuple (args_R args) tuple \<and> (\<forall>i\<in>{0..<length auxlist}.
      let (t, l, r) = auxlist ! i in mem (args_ivl args) (cur - t) \<longrightarrow>
      tuple \<in> r \<or> (\<exists>j\<in>{i<..<length auxlist}.
        join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j)) (restrict (args_L args) (args_R args) tuple)))}"
    (is "{tuple. ?A tuple} = {tuple. ?B tuple}")
  proof (intro Collect_cong)
    fix tuple
    show "?A tuple \<longleftrightarrow> ?B tuple"
    proof (cases "wf_tuple (args_R args) tuple")
      case True
      show ?thesis
        using fst_nth jc[OF _ True]
        by (auto simp: Let_def case_prod_beta)
    qed simp
  qed
  moreover have "args_L (trigger_args args) = args_R args"
    using False by simp
  ultimately show ?thesis
    unfolding map_eq trigger_results.simps trigger_args_simps(1-3) len
    by (simp only:)
qed

lemma valid_init_mmtaux: "(
    if (mem I 0)
      then
        set L \<subseteq> set R
      else 
        set L = set R
    ) \<Longrightarrow>
    distinct L \<Longrightarrow> distinct R \<Longrightarrow>
    \<not>mem I 0 \<longrightarrow> pos \<Longrightarrow>
    let args = init_args I n L R pos agg in
    valid_mmtaux args 0 (init_mmtaux args) []"
  using valid_init_nmtaux[of I "if mem I 0 then L else R" R pos n agg]
  by (auto simp: valid_mmtaux_def trigger_args_def init_args_def init_mmtaux_def Let_def split: if_splits)

lemma valid_update_mmtaux:
  assumes "nt \<ge> cur" "table (args_L args) l" "table (args_R args) r" "valid_mmtaux args cur aux auxlist"
  shows "valid_mmtaux args nt (update_mmtaux args nt l r aux)
    ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])"
proof -
  have map_filter: "map (\<lambda>(t, l, r). (t, trigger_lhs args l, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs) =
    filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (map (\<lambda>(t, l, r). (t, trigger_lhs args l, r)) xs)" for xs :: "event_data mtaux"
    by (induction xs) auto
  have "valid_nmtaux (trigger_args args) nt (update_nmtaux (trigger_args args) nt (trigger_lhs args l) r aux)
    (filter (\<lambda>(t, _). memR (args_ivl (trigger_args args)) (nt - t)) (map (\<lambda>(t, l, r). (t, trigger_lhs args l, r)) auxlist) @
     [(nt, trigger_lhs args l, r)])"
    using assms(4) unfolding valid_mmtaux_def
    by (intro valid_update_nmtaux[OF assms(1) table_trigger_lhs[OF assms(2)]]) (simp_all add: assms(3))
  then show ?thesis
    using assms unfolding valid_mmtaux_def update_mmtaux_def
    by (auto simp: map_filter)
qed

lemma valid_result_mmtaux:
  assumes "valid_mmtaux args cur aux auxlist"
  shows "result_mmtaux args aux = trigger_results args cur auxlist"
proof -
  have "result_mmtaux args aux = trigger_results (trigger_args args) cur (map (\<lambda>(t, l, r). (t, trigger_lhs args l, r)) auxlist)"
    using assms valid_result_nmtaux unfolding valid_mmtaux_def result_mmtaux_def by blast
  also have "\<dots> = trigger_results args cur auxlist"
    using assms unfolding valid_mmtaux_def by (intro trigger_results_trigger_args) auto
  finally show ?thesis .
qed

(*<*)
end
(*>*)
