(*<*)
theory Optimized_Agg_Valid
  imports Optimized_Agg
begin
(*>*)

lemma mset_conv_comm:
  "comp_fun_commute_on UNIV (\<lambda>(t, m) b. case f t of None \<Rightarrow> b | Some k \<Rightarrow> replicate_mset (the_enat m) k + b)"
  by(unfold_locales) (auto split:option.splits)

lemma mset_conv_insert_remove:
  assumes "(t, enat n) \<in> M" and "f t \<in> range Some" and "(t, enat (n + 1)) \<notin> M" and "finite M"
  shows "mset_conv f (Set.insert (t, enat (n + 1)) (M - {(t, enat n)})) = add_mset (the (f t)) (mset_conv f M)"
proof -
  have *: "finite (M - {(t, enat n)})" using assms(4) by auto
  have **: "(t, enat (n + 1)) \<notin> (M - {(t, enat n)})" using assms(3) by auto
  have ***: "(t, enat n) \<notin> (M - {(t, enat n)})" by auto
  have simp1: "mset_conv f (Set.insert (t, enat (n + 1)) (M - {(t, enat n)})) = replicate_mset (the_enat (n + 1)) (the (f t)) + mset_conv f (M - {(t, enat n)})"
    using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm _ * **, of f] assms(2) by(auto simp add:mset_conv_def)
  then have "mset_conv f (Set.insert (t, enat n) (M - {(t, enat n)})) = replicate_mset (the_enat n) (the (f t)) + mset_conv f (M - {(t, enat n)})"
    using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm _ * ***, of f] assms(2) by(auto simp add:mset_conv_def) 
  moreover have "Set.insert (t, enat n) (M - {(t, enat n)}) = M" using assms(1) by auto
  ultimately have "mset_conv f M = replicate_mset (the_enat n) (the (f t)) + mset_conv f (M - {(t, enat n)})" by auto
  then show ?thesis using simp1 by simp
qed

lemma mset_conv_insert_remove':
  assumes "(t, enat (n + 1)) \<in> M" and "f t \<in> range Some" and "(t, enat n) \<notin> M" and "finite M"
  shows "mset_conv f (Set.insert (t, enat n) (M - {(t, enat (n + 1))})) + {#the (f t)#} = mset_conv f M"
proof -
  have *: "finite (M - {(t, enat (n + 1))})" using assms(4) by auto
  have **: "(t, enat n) \<notin> (M - {(t, enat (n + 1))})" using assms(3) by auto
  have ***: "(t, enat (n + 1)) \<notin> (M - {(t, enat (n + 1))})" by auto
  have simp1: "mset_conv f (Set.insert (t, enat n) (M - {(t, enat (n + 1))})) = replicate_mset (the_enat n) (the (f t)) + mset_conv f (M - {(t, enat (n + 1))})"
    using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm _ * **, of f] assms(2) by(auto simp add:mset_conv_def)
  then have "mset_conv f (Set.insert (t, enat (n + 1)) (M - {(t, enat (n + 1))})) = replicate_mset (the_enat (n + 1)) (the (f t)) + mset_conv f (M - {(t, enat (n + 1))})"
    using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm _ * ***, of f] assms(2) by(auto simp add:mset_conv_def) 
  moreover have "Set.insert (t, enat (n + 1)) (M - {(t, enat (n + 1))}) = M" using assms(1) by auto
  ultimately have "mset_conv f M = replicate_mset (the_enat (n + 1)) (the (f t)) + mset_conv f (M - {(t, enat (n + 1))})" by auto
  then show ?thesis using simp1 by auto
qed

lemma unique_term_multiset: "(t, y1) \<in> group_multiset k b cs f X \<Longrightarrow> y2 \<noteq> y1 \<Longrightarrow> (t, y2) \<notin> group_multiset k b cs f X"
proof rule
  assume term_in: "(t, y1) \<in> group_multiset k b cs f X" and not_eq: "y2 \<noteq> y1" and term_in_2: "(t, y2) \<in> group_multiset k b cs f X"
  define group where [simp]: "group = Set.filter (\<lambda>x. agg_key b cs x = k) X"
  have "y2 = ecard (Set.filter (\<lambda>x. meval_trm cs f x = t) group)" using term_in_2 by auto
  moreover have "y1 = ecard (Set.filter (\<lambda>x. meval_trm cs f x = t) group)" using term_in by auto
  ultimately show False using not_eq by auto
qed

lemma valid_init_maggaux_unfolded: 
   "let (v', aux') = init_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> in
    if v' then valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> aux' {} else True"
  by(cases "fst \<omega>"; cases "snd \<omega>"; auto simp: type_restr_def) 

lemma valid_init_maggaux: "let (v', aux') = init_maggaux args in
                           if v' then valid_maggaux args aux' {} else True"
  using valid_init_maggaux_unfolded by(cases args) fast

lemma valid_finite_group_mset:
  assumes "finite X"
  shows "valid_finite_mset (group_multiset k b cs f X)"
  using assms by(auto simp:valid_finite_mset_def ecard_def zero_enat_def)+ 

lemma insort_mset_bulk_insort:
  assumes "ID ccompare = Some (c :: (event_data \<times> enat) comparator)" 
  and "ID ccompare = Some (c' :: event_data comparator)" 
  and "valid_finite_mset (Set.insert (e, enat n) F)"
  and "(e, enat n) \<notin> F"
  shows "concat (map (\<lambda>(x, c). replicate (the_enat c) x) (linorder.insort (le_of_comp c) (e, enat n) (linorder.sorted_list_of_set (le_of_comp c) F))) =
     ((linorder.insort (le_of_comp c') e) ^^ n) (concat (map (\<lambda>(x, c). replicate (the_enat c) x) (linorder.sorted_list_of_set (le_of_comp c) F)))" (is "?lhs = ?rhs")
proof -
  let ?xs = "linorder.sorted_list_of_set (le_of_comp c) F"
  let ?f = "\<lambda>(x, c). replicate (the_enat c) x"
  let ?x = "(e, enat n)"
  interpret linorder "(le_of_comp c)" "(lt_of_comp c)"
    using assms(1) ID_ccompare by auto
  note c' = ID_ccompare'[OF assms(2)] 
  note c'_class = comparator.linorder[OF c']
  have finite: "finite F" using assms(3) by (auto simp:valid_finite_mset_def)
  then have "(e, enat n) \<notin> set ?xs" using assms(4) set_sorted_list_of_set by auto
  moreover have "sorted_wrt (le_of_comp c) (sorted_list_of_set F)" 
    using sorted_sorted_list_of_set by(auto)
  ultimately obtain xs ys where split: "insort ?x ?xs = xs @ (e, enat n) # ys \<and> ?xs = xs @ ys \<and> (\<forall>k. k \<in> set xs \<longrightarrow> (lt_of_comp c) k ?x) \<and> (\<forall>k. k \<in> set ys \<longrightarrow> (lt_of_comp c) ?x k)"
    using split_insort[of ?x ?xs] by blast
  then have concat: "?xs = xs @ ys" by auto
  have "F = set (xs @ ys)" using split set_sorted_list_of_set[OF finite] by auto
  then have subs: "set xs \<subseteq> F \<and> set ys \<subseteq> F" by auto
  have inv1: "(\<forall>k. k \<in> set (concat (map ?f xs)) \<longrightarrow> (lt_of_comp c') k e)" 
  proof (rule allI, rule impI)
    fix k
    assume "k \<in> set (concat (map ?f xs))"
    moreover have "\<And>b. (k, b) \<in> set xs \<Longrightarrow> lt_of_comp c' k e"
    proof -
      fix b
      assume *: "(k, b) \<in> set xs"
      then have "k \<noteq> e" using assms(3) subs by(simp add:valid_finite_mset_def) (metis assms(4) subsetD)
      then show "lt_of_comp c' k e" 
        using split * ccomp_eq[OF assms(1), OF assms(2), of k e] lt_of_comp_def[of c] lt_of_comp_def[of c'] by auto metis
    qed
    ultimately show "(lt_of_comp c') k e" by(auto)
  qed
  have inv2: "(\<forall>k. k \<in> set (concat (map ?f ys)) \<longrightarrow> (lt_of_comp c') e k)" 
  proof (rule allI, rule impI)
    fix k
    assume "k \<in> set (concat (map ?f ys))"
    moreover have "\<And>b. (k, b) \<in> set ys \<Longrightarrow> lt_of_comp c' e k"
    proof -
      fix b
      assume *: "(k, b) \<in> set ys"
      then have "k \<noteq> e" using assms(3) subs by(simp add:valid_finite_mset_def) (metis assms(4) subsetD)
      then show "lt_of_comp c' e k" 
        using split * ccomp_eq[OF assms(1), OF assms(2), of e k] lt_of_comp_def[of c] lt_of_comp_def[of c'] by auto metis
    qed
    ultimately show "(lt_of_comp c') e k" by(auto)
  qed
  have "?lhs = concat (map ?f xs) @ (replicate n e) @ concat (map ?f ys)" using split by(auto)
  moreover have "?rhs = ((linorder.insort (le_of_comp c') e) ^^ n) (concat (map ?f xs) @ concat (map ?f ys))" using concat by auto
  ultimately show ?thesis using linorder.bulk_insort[OF c'_class, OF inv1, OF inv2] by(auto)
qed

lemma flatten_multiset_not_empty: 
  assumes valid_map: "valid_aggmap g b cs f m X"
  and finite: "finite X"
  and in_map: "k \<in> Mapping.keys m"
  shows "flatten_multiset (group_multiset k b cs f X) \<noteq> []"
proof -
  define M where [simp]: "M = group_multiset k b cs f X"
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)" 
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  note c = ID_ccompare'[OF c_def] 
  note c_class = comparator.linorder[OF c]
  define M_list where [simp]: "M_list = linorder.sorted_list_of_set (le_of_comp c) M"
  obtain elem where elem_prop: "elem \<in> X \<and> agg_key b cs elem = k" using in_map valid_map imageE[of k "agg_key b cs" X] by auto
  then obtain m where m_prop: "(meval_trm cs f elem, m) \<in> M" 
    by auto
  define group where [simp]: "group = Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (Set.filter (\<lambda>x. agg_key b cs x = k) X)"
  have "ecard group \<noteq> 0" using finite elem_prop by (auto simp:ecard_def zero_enat_def) 
  then have m_pos: "m > 0 \<and> m \<noteq> \<infinity>" 
    using elem_prop m_prop finite  by (auto simp: ecard_def)
  then have "the_enat m > 0"
    by (cases m) (simp_all add: zero_enat_def)
  then obtain n where n_def: "the_enat m = Suc n" using gr0_implies_Suc by auto
  have finite_m: "finite M" using finite by auto
  then have "(meval_trm cs f elem, m) \<in> set (linorder.sorted_list_of_set (le_of_comp c) M)"
    using m_prop linorder.set_sorted_list_of_set[OF c_class] by auto
  then show ?thesis 
    using finite_m n_def by (simp add:flatten_multiset_def csorted_list_of_set_def c_def) force
qed

lemma valid_list_aux_remove:
  assumes "valid_list_aux' l s"
  shows "valid_list_aux' (((remove_treelist t) ^^ n) l) (s - replicate_mset n t)"
  using assms by (simp add: valid_list_aux'_def mset_remove_treelist_funpow)


lemma unpack_insort:
  assumes "ID ccompare = Some (c :: event_data comparator)" 
  and "\<forall>t. (t \<in> set xs \<longrightarrow> (\<exists>k. f t = Some k))"
  and "\<forall>e. e \<in> set xs \<longrightarrow> c t e = comp_of_ords (\<le>) (<) (the (f t)) (the (f e))"
  shows "map (\<lambda>a. the (f a)) (linorder.insort (le_of_comp c) t xs) = insort1 (the (f t)) (map (\<lambda>a. the (f a)) xs)"
proof -
  interpret linorder "le_of_comp c" "lt_of_comp c"
    using ID_ccompare[OF assms(1)] by auto
  show ?thesis using assms(2-3)
  proof(induction xs)
    case Nil
    then show ?case using insort_key_def by auto
  next
    case (Cons a xs)
    then obtain k where a_def: "f a = Some k" by auto
    let ?t = "(the \<circ> f) t"
    have *: "\<forall>t. (t \<in> set xs \<longrightarrow> (\<exists>k. f t = Some k))" using Cons by auto
    show ?case 
    proof(cases "(le_of_comp c) t a")
      case True
      then have "?t \<le> k" using Cons(3) a_def 
        by (metis comp_of_ords_def insertI1 le_of_comp_def linorder_class.le_cases list.set(2) o_apply option.sel order.simps(9) order_class.leD)
      then show ?thesis using True by(simp add:a_def) 
    next
      case False
      then have "?t > k" using Cons(3) a_def
        by (metis a_def comp_eq_dest_lhs comp_of_ords_def comp_of_ords_def comp_of_ords_of_le_lt linorder_class.not_le list.set_intros(1) local.less_imp_le option.sel order.case(1) order.simps(6) order.simps(9))
      then show ?thesis using False Cons(1)[OF *] Cons order_class.leD by(simp add:a_def) force
    qed
  qed
qed

lemma bulk_unpack_insort:
  assumes "ID ccompare = Some (c :: event_data comparator)" 
  and "\<forall>e. (e \<in> (set xs) \<union> {t} \<longrightarrow> (\<exists>k. f e = Some k))"
  and "\<forall>e. e \<in> (set xs) \<union> {t} \<longrightarrow> c t e = comp_of_ords (\<le>) (<) (the (f t)) (the (f e))"
  shows "map (\<lambda>a. the (f a)) ((linorder.insort (le_of_comp c) t ^^ n) xs)
         = (insort1 ((the \<circ> f) t) ^^ n) (map (the \<circ> f) xs)"
  using assms(2-3)
proof(induction n arbitrary:xs)
  case 0
  then show ?case by auto
next
  case (Suc n)
  interpret linorder "le_of_comp c" "lt_of_comp c"
    using ID_ccompare[OF assms(1)] by auto
  have *: "\<forall>x. (x \<in> set ((linorder.insort (le_of_comp c) t ^^ n) xs) \<longrightarrow> (\<exists>k. f x = Some k))"
    using Suc(2) assms(3) set_insort_key[of _ t] by(induction n) auto
  have **: "\<forall>e. e \<in> set ((local.insort t ^^ n) xs) \<longrightarrow> c t e = comp_of_ords (\<le>) (<) (the (f t)) (the (f e))"
    using Suc(3) set_insort_key[of _ t] by(induction n) (auto) 
  show ?case using unpack_insort[OF assms(1), OF *, OF **] Suc by auto
qed

lemma sort_flatten_mset_eq:
  assumes "ID ccompare = Some (c' :: event_data comparator)" 
  and "valid_list_aux' l (mset_conv f s)"
  and "valid_finite_mset s"
  and "\<forall>t m. ((t, m) \<in> s \<longrightarrow> (\<exists>k. f t = Some k))"
  and "\<forall>t1 m1 t2 m2. ((t1, m1) \<in> s \<and> (t2, m2) \<in> s \<longrightarrow>  c' t1 t2 = comp_of_ords (\<le>) (<) (the (f t1)) (the (f t2)))"
  shows  "unpack (sort_treelist l) = map (\<lambda>a. the (f a)) (flatten_multiset s)"
proof -
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)" 
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  note c_class = comparator.linorder[OF ID_ccompare'[OF c_def]]
  note c'_class = comparator.linorder[OF ID_ccompare'[OF assms(1)]]
  have "finite s" using assms(3) by (auto simp:valid_finite_mset_def)
  then show ?thesis using assms(2-5)
  proof(induction s arbitrary:l)
    case empty
    then have "l = empty_treelist" by(auto simp:valid_list_aux'_def mset_conv_def) (metis Rep_treelist_inject empty_treelist.rep_eq mset_treelist.rep_eq mset_zero_iff)
    then have "unpack (sort_treelist l) = []" by transfer auto
    then show ?case 
       using linorder.sorted_list_of_set_empty[OF c_class] by (auto simp:flatten_multiset_def csorted_list_of_set_def c_def)
  next
    case (insert x F)
    obtain t i where x_def: "x = (t, enat i)" 
      using insert(5) by(simp add:valid_finite_mset_def) (metis surj_pair)
    let ?t = "(the \<circ> f) t"
    let ?l_removed = "((remove_treelist ?t) ^^ i) l"
    have valid: "valid_finite_mset (Set.insert (t, enat i) F)" using x_def insert(5) by auto
    have notin: "(t, enat i) \<notin> F" using x_def insert(2) by auto
    have "mset_conv f F = mset_conv f (Set.insert x F) - replicate_mset i ?t"
      using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of f] _ insert(1) insert(2)] insert(6) x_def
      by (auto simp:mset_conv_def) fastforce
    then have "valid_list_aux' ?l_removed (mset_conv f F)" 
      using valid_list_aux_remove[OF insert(4)] by simp
    moreover have valid_f: "valid_finite_mset F" using insert(5)
      unfolding valid_finite_mset_def using insert.hyps(1) by blast
    ultimately have IH: "unpack (sort_treelist ?l_removed) = map (the \<circ> f) (flatten_multiset F)" using insert
      by fastforce
    have *: "\<forall>t. t \<in> set (flatten_multiset F) \<longrightarrow> (\<exists>k. f t = Some k)" "\<exists>k. f t = Some k" 
      using mset_prop_unfold[OF c_def, of F f] valid_f insert.prems(3) x_def by blast+
    have **: "\<forall>e. e \<in> (set (flatten_multiset F)) \<union> {t} \<longrightarrow> c' t e = comp_of_ords (\<le>) (<) (the (f t)) (the (f e))"
      using mset_multi_prop_unfold[OF c_def assms(1) insert(7) insert(5)] x_def
            set_insert_flatten_mset[OF c_def valid notin] by(simp) 
    have "flatten_multiset (Set.insert x F) = ((linorder.insort (le_of_comp c') t) ^^ i) (flatten_multiset F)"
      using insort_mset_bulk_insort[OF c_def, OF assms(1)] insert x_def linorder.sorted_list_of_set_insert[OF c_class]
      by (simp add: c_def csorted_list_of_set_def flatten_multiset_def)
    then have simp1: "map (\<lambda>a. the (f a)) (flatten_multiset (Set.insert x F)) = (insort1 ((the \<circ> f) t) ^^ i) (map (the \<circ> f) (flatten_multiset F))"
       using bulk_unpack_insort[OF assms(1) _ **] * by simp
    have *: "(count \<circ> mset_treelist) l ?t \<ge> i" using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of f] _ insert(1) insert(2)]
       insert(4) insert(6) by(auto simp:x_def valid_list_aux'_def mset_conv_def) fastforce
    have simp2:"unpack (sort_treelist l) = ((insort1 ?t) ^^ i) (map (the \<circ> f) (flatten_multiset F))" unfolding sort_insert_remove[OF *] 
      using IH by(transfer; auto)
    show ?case by(simp only:simp1) (simp add:simp2) 
  qed                        
qed

lemma int_cmp_eq:
  assumes "ID ccompare = Some (c :: event_data comparator)"
  and "t1 \<in> range EInt"
  and "t2 \<in> range EInt"
  shows "c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_int t1)) (the (unpack_int t2))"
proof -
  have "c = comparator_event_data" using assms(1) option.sel by (simp add: ID_code ccompare_event_data_def)
  moreover have *: "comparator_of = comp_of_ords (\<le>) (<)" using comp_of_ords_of_le_lt le_lt_comparator_of by metis
  ultimately show ?thesis using assms(2-3) by(auto simp:unpack_int_def *) 
qed

lemma str_cmp_eq:
  assumes "ID ccompare = Some (c :: event_data comparator)"
  and "t1 \<in> range EString"
  and "t2 \<in> range EString"
  shows "c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_string t1)) (the (unpack_string t2))"
proof -
  have "c = comparator_event_data" using assms(1) option.sel by (simp add: ID_code ccompare_event_data_def)
  moreover have *: "comparator_of = comp_of_ords (\<le>) (<)" using comp_of_ords_of_le_lt le_lt_comparator_of by metis
  ultimately show ?thesis using assms(2-3) by(auto simp:unpack_string_def *) 
qed

lemma meval_in_set:
  assumes "elem \<in> X"
  and "agg_key b cs elem = k"
  and "finite X"
  shows "meval_trm cs f elem \<in> set (flatten_multiset (group_multiset k b cs f X))"
proof -
  have finite: "finite (group_multiset k b cs f X)" using valid_finite_group_mset[OF assms(3), of k b cs f] by (auto simp:valid_finite_mset_def)
  have "meval_trm cs f elem \<in> meval_trm cs f ` Set.filter (\<lambda>x. agg_key b cs x = k) X"
    using assms(1-2) by simp
  then obtain m where in_mset: "(meval_trm cs f elem, m) \<in> group_multiset k b cs f X" 
    by simp blast
  then obtain i where m_def: "m = enat i" "i > 0" using valid_finite_group_mset[OF assms(3), of k b cs f]
    by(simp add:valid_finite_mset_def) (metis (no_types, lifting) enat_0_iff(1) gr0I)
  show ?thesis using meval_in_set_aux[OF _ finite m_def(2), of "meval_trm cs f elem"] assms(1) in_mset m_def(1) by auto
qed

lemma in_mset_in_list_int:
  assumes "EInt i \<in> set (flatten_multiset (group_multiset k b cs f X))"
  and "finite X"
  and "valid_list_aux (LInt li) (group_multiset k b cs f X) IntT"
  shows "i \<in> set_treelist li"
proof -
  obtain c where c_def: "ID ccompare = Some (c :: event_data comparator)" 
    by (simp add: ID_def ccompare_event_data_def split:if_splits option.splits)
  have *: "valid_list_aux' li (mset_conv unpack_int (group_multiset k b cs f X))" using assms(3) by(auto simp:valid_list_aux_def int_mset_conv_def)
  have **: "\<forall>t1 m1 t2 m2.
     (t1, m1) \<in> group_multiset k b cs f X \<and> (t2, m2) \<in> group_multiset k b cs f X \<longrightarrow>
     c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_int t1)) (the (unpack_int t2))" by (metis assms(3) c_def int_cmp_eq list_aux.case(1) type_restr_mset_def valid_list_aux_def)
  have ***: "\<forall>t m. (t, m) \<in> group_multiset k b cs f X \<longrightarrow> (\<exists>k. unpack_int t = Some k)" by (metis (no_types, lifting) assms(3) event_data.simps(10) imageE list_aux.case(1) type_restr_mset_def unpack_int_def valid_list_aux_def)
  have "the (unpack_int (EInt i)) \<in> set (map (\<lambda>a. the (unpack_int a)) (flatten_multiset (group_multiset k b cs f X)))" 
    using assms(1) by simp
  then show ?thesis using sort_flatten_mset_eq[OF c_def * valid_finite_group_mset[OF assms(2)] *** **] 
    by(simp add:unpack_int_def; transfer) (metis id_def image_set set_sort) 
qed

lemma in_mset_in_list_str:
  assumes "EString i \<in> set (flatten_multiset (group_multiset k b cs f X))"
  and "finite X"
  and "valid_list_aux (LString li) (group_multiset k b cs f X) StringT"
  shows "i \<in> set_treelist li"
proof -
  obtain c where c_def: "ID ccompare = Some (c :: event_data comparator)" 
    by (simp add: ID_def ccompare_event_data_def split:if_splits option.splits)
  have *: "valid_list_aux' li (mset_conv unpack_string (group_multiset k b cs f X))" using assms(3) by(auto simp:valid_list_aux_def str_mset_conv_def)
  have **: "\<forall>t1 m1 t2 m2.
     (t1, m1) \<in> group_multiset k b cs f X \<and> (t2, m2) \<in> group_multiset k b cs f X \<longrightarrow>
     c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_string t1)) (the (unpack_string t2))" by (metis assms(3) c_def str_cmp_eq list_aux.case(2) type_restr_mset_def valid_list_aux_def)
  have ***: "\<forall>t m. (t, m) \<in> group_multiset k b cs f X \<longrightarrow> (\<exists>k. unpack_string t = Some k)" by (metis (no_types, lifting) assms(3) event_data.simps(12) image_iff list_aux.case(2) type_restr_mset_def unpack_string_def valid_list_aux_def)
  have "the (unpack_string (EString i)) \<in> set (map (\<lambda>a. the (unpack_string a)) (flatten_multiset (group_multiset k b cs f X)))" 
    using assms(1) by simp
  then show ?thesis using sort_flatten_mset_eq[OF c_def * valid_finite_group_mset[OF assms(2)] *** **] 
    by(simp add:unpack_string_def; transfer) (metis id_def image_set set_sort) 
qed

lemma other_evals_unchanged:
  assumes elem_group: "agg_key b cs elem = k"
  and diff_group: "x \<noteq> meval_trm cs f elem"
  shows "(x, y) \<in> group_multiset k b cs f (Set.insert elem X) \<longleftrightarrow> (x, y) \<in> group_multiset k b cs f X"
proof
  define old_group where [simp]: "old_group = group k b cs X"
  define new_group where [simp]: "new_group = group k b cs (X \<union> {elem})"
  have aux1: "\<And>x. x \<noteq> meval_trm cs f elem \<Longrightarrow> Set.filter (\<lambda>xa. meval_trm cs f xa = x) new_group = Set.filter (\<lambda>xa. meval_trm cs f xa = x) old_group" by auto
  assume assm: "(x, y) \<in> group_multiset k b cs f (Set.insert elem X)"
  then have x_old_eval: "x \<in> meval_trm cs f ` old_group" using diff_group by auto
  have "y = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = x) new_group)" using assm by auto
  then have "y =  ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = x) old_group)" using aux1 diff_group by auto
  then show "(x, y) \<in>  group_multiset k b cs f X" using x_old_eval by auto
next
  define old_group where [simp]: "old_group = group k b cs X"
  define new_group where [simp]: "new_group = group k b cs (X \<union> {elem})"
  have aux1: "\<And>x. x \<noteq> meval_trm cs f elem \<Longrightarrow> Set.filter (\<lambda>xa. meval_trm cs f xa = x) new_group = Set.filter (\<lambda>xa. meval_trm cs f xa = x) old_group" by auto
  assume assm: "(x, y) \<in>  group_multiset k b cs f X"
  then have x_old_eval: "x \<in> meval_trm cs f ` old_group" by auto
  have "y = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = x) old_group)" using assm by auto
  then have "y =  ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = x) new_group)" using aux1 diff_group by auto
  then show "(x, y) \<in> group_multiset k b cs f (Set.insert elem X)" using x_old_eval by auto
qed

lemma multiset_new_term_insert:
  assumes elem_group: "agg_key b cs elem = k"
  and new_term_eval: "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) = {}"
  shows "group_multiset k b cs f (Set.insert elem X) = Set.insert (meval_trm cs f elem, 1) (group_multiset k b cs f X)"
proof -
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  define old_group where [simp]: "old_group = group k b cs X"
  define new_group where [simp]: "new_group = group k b cs updated_data"
  define old_evals where "old_evals = meval_trm cs f ` old_group"
  have aux: "Set.filter (\<lambda>x. agg_key b cs x = k) (Set.insert elem X) = Set.insert elem old_group" using elem_group by auto
  have aux1: "\<And>x. x \<noteq> meval_trm cs f elem \<Longrightarrow> Set.filter (\<lambda>xa. meval_trm cs f xa = x) new_group = Set.filter (\<lambda>xa. meval_trm cs f xa = x) old_group" by auto
  have aux2: "meval_trm cs f elem \<notin> old_evals" using new_term_eval by (auto simp: old_evals_def)
  moreover have "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) new_group = {elem}" using new_term_eval elem_group by auto
  moreover have "ecard {elem} = 1" using enat_1 by (auto simp:ecard_def)
  moreover have "(\<lambda>x. (x, ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = x) new_group))) ` old_evals = 
                 (\<lambda>x. (x, ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = x) old_group))) ` old_evals"
    using other_evals_unchanged by (metis (mono_tags, lifting) aux1 aux2 image_cong)
  ultimately show "group_multiset k b cs f (Set.insert elem X) = Set.insert (meval_trm cs f elem, 1) (group_multiset k b cs f X)" using aux
    by (simp add: old_evals_def del: Set.filter_eq)
qed

lemma single_term_in_multiset:
  assumes elem_group: "agg_key b cs elem = k"
  and single_term_eval: "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) = {elem}"
  shows "(meval_trm cs f elem, 1) \<in> group_multiset k b cs f X"
proof -
  have "elem \<in> group k b cs X" using single_term_eval elem_group by auto
  then obtain v' where v'_def: "(meval_trm cs f elem, v') \<in> group_multiset k b cs f X" by auto
  then have "v' = ecard (Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X))" by auto
  then have v'_val: "v' = 1" using single_term_eval by(simp add: ecard_def one_enat_def) 
  then show "(meval_trm cs f elem, 1) \<in> group_multiset k b cs f X" using v'_def by auto
qed

lemma multiset_single_term_remove:
  assumes elem_group: "agg_key b cs elem = k"
  and single_term_eval: "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) = {elem}"
  shows "group_multiset k b cs f (X - {elem}) = (group_multiset k b cs f X) - {(meval_trm cs f elem, 1)}"
proof (rule set_eqI, rule iffI)
  fix x
  assume x_in_M: "x \<in> group_multiset k b cs f (X - {elem})"
  then obtain t v where x_def: "x = (t, v)" by fastforce
  have "t \<in> meval_trm cs f ` group k b cs (X - {elem})" using x_def x_in_M by auto
  moreover have "elem \<notin> group k b cs (X - {elem})" by auto
  ultimately have noteq: "t \<noteq> meval_trm cs f elem" using imageE single_term_eval by auto
  then have "x \<noteq> (meval_trm cs f elem, 1)" using x_def by force
  moreover have "x \<in> group_multiset k b cs f X"
    using  x_def by (metis elem_group insert_Diff_single noteq other_evals_unchanged x_in_M)
  ultimately show "x \<in>  (group_multiset k b cs f X) - {(meval_trm cs f elem, 1)}" 
    by auto
next
  fix x
  assume x_in_oldM: "x \<in> (group_multiset k b cs f X) - {(meval_trm cs f elem, 1)}"
  then obtain t v where x_def: "x = (t, v)" by (meson surj_pair)
  have "elem \<in> group k b cs X" using single_term_eval elem_group by auto
  have "(meval_trm cs f elem, 1) \<in> group_multiset k b cs f X" using single_term_in_multiset elem_group single_term_eval by auto
  then have "t \<noteq> meval_trm cs f elem" using  x_def x_in_oldM by (metis DiffE insertI1 unique_term_multiset)
  then show "x \<in> group_multiset k b cs f (X - {elem})" using x_def 
    using other_evals_unchanged[of b cs elem k t f v] x_in_oldM elem_group
    by (metis DiffD1 insert_Diff_single)
qed

lemma multiset_multiple_term_remove:
  assumes elem_group: "agg_key b cs elem = k"
  and old_term_eval: "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) \<noteq> {elem}"
  and old_val: "(meval_trm cs f elem, enat y) \<in> group_multiset k b cs f X" 
  and inside: "elem \<in> X"
  and finite: "finite X"
  shows "group_multiset k b cs f (X - {elem}) = 
         Set.insert (meval_trm cs f elem, enat (y - 1)) ((group_multiset k b cs f X) - {(meval_trm cs f elem, enat y)})"
proof (rule set_eqI, rule iffI)
  fix x
  assume x_in_M: "x \<in> group_multiset k b cs f (X - {elem})"
  then obtain t v where x_def: "x = (t, v)" by fastforce
  define updated_data where "updated_data = X - {elem}"
  define old_group where "old_group = group k b cs X"
  define new_group where "new_group = group k b cs updated_data"
  define old_evals where "old_evals = meval_trm cs f ` old_group"
  have "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) \<noteq> {}" using inside elem_group by auto
  then obtain elem' where elem'_def:  "elem' \<in> Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) \<and> elem \<noteq> elem'" 
    using old_term_eval by blast
  have group_ins: "new_group = old_group - {elem}" using elem_group by (auto simp: new_group_def old_group_def updated_data_def)
  have y_card: "enat y = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) old_group)" using old_val by (auto simp: old_group_def)
  let ?S = "Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) old_group"
  have S_fin: "finite ?S" using finite by (simp add: old_group_def)
  have elem_in_S: "elem \<in> ?S" using inside elem_group by (simp add: old_group_def)
  have y_eq: "y = card ?S" using y_card S_fin by (simp add: ecard_def)
  have "Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) new_group = ?S - {elem}"
    using group_ins by fastforce
  then have correct_card: "enat (y - 1) = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) new_group)" 
    using S_fin elem_in_S y_eq by (simp add: ecard_def)
  obtain v' where v'_def: "(meval_trm cs f elem, v') \<in> group_multiset k b cs f updated_data" using elem'_def 
    by (simp add: updated_data_def) (metis (mono_tags, lifting) image_eqI mem_Collect_eq)
  then have "v' = y - 1" using correct_card by (auto simp: new_group_def)
  then have aux1: "(meval_trm cs f elem, enat (y - 1)) \<in> group_multiset k b cs f updated_data" using v'_def by auto
  have "card ?S > 0" using S_fin elem_in_S card_gt_0_iff by blast
  then have "enat y \<noteq> enat (y - 1)" using y_eq by simp
  then have aux2: "(meval_trm cs f elem, enat y) \<notin> group_multiset k b cs f (updated_data)" 
    using unique_term_multiset[of "meval_trm cs f elem" "enat (y - 1)" k b cs f updated_data y] y_card aux1 by auto
  show "x \<in> Set.insert (meval_trm cs f elem, enat (y - 1)) ((group_multiset k b cs f X) - {(meval_trm cs f elem, enat y)})"
  proof (cases "t = meval_trm cs f elem")
    case True
    then have "v = y - 1" using x_in_M x_def aux1 using unique_term_multiset updated_data_def by blast
    then show ?thesis using x_def x_in_M True by auto
  next
    case False
    then show ?thesis using other_evals_unchanged by (metis Diff_iff elem_group insertI2 insert_Diff inside old.prod.inject singletonD x_def x_in_M)
  qed
next
  fix x
  assume x_in_oldM: "x \<in> Set.insert (meval_trm cs f elem, enat (y - 1)) ((group_multiset k b cs f X) - {(meval_trm cs f elem, enat y)})"
  then obtain t v where x_def: "x = (t, v)" by force
  define updated_data where "updated_data = X - {elem}"
  define old_group where "old_group = group k b cs X"
  define new_group where "new_group = group k b cs updated_data"
  define old_evals where "old_evals = meval_trm cs f ` old_group"
  have "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) \<noteq> {}" using inside elem_group by auto
  then obtain elem' where elem'_def:  "elem' \<in> Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) \<and> elem \<noteq> elem'" 
    using old_term_eval by blast
  have group_ins: "new_group = old_group - {elem}" using elem_group by (auto simp: new_group_def old_group_def updated_data_def)
  have y_card: "enat y = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) old_group)" using old_val by (auto simp: old_group_def)
  have "Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) new_group = (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) old_group) - {elem}"
    using group_ins by fastforce
  then have correct_card: "enat (y - 1) = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) new_group)" 
    using y_card
    by (smt (verit, ccfv_threshold) Diff_iff Optimized_Agg.group_def
        Set.filter_eq assms(4) card.insert ecard_def elem_group
        enat.simps(1,3) finite_insert insertCI insert_Diff
        mem_Collect_eq old_group_def)
  obtain v' where v'_def: "(meval_trm cs f elem, v') \<in> group_multiset k b cs f updated_data" using elem'_def
    by (metis (mono_tags, lifting) Set.filter_eq group_ins
        group_multiset_def imageI insert_Diff_single insert_compr
        mem_Collect_eq new_group_def old_group_def)
  then have "v' = y - 1" using correct_card by (auto simp: new_group_def)
  then have aux1: "(meval_trm cs f elem, y - 1) \<in> group_multiset k b cs f updated_data" using v'_def by auto
  show "x \<in> group_multiset k b cs f (X - {elem})" 
  proof (cases "t = meval_trm cs f elem")
    case True
    then have "v = y - 1" using x_in_oldM x_def by (metis DiffE insertE old.prod.inject old_val singleton_iff unique_term_multiset)
    then show ?thesis using True aux1 x_def updated_data_def by fastforce
  next
    case False
    then show ?thesis by (metis DiffD1 elem_group insertE insert_Diff inside old.prod.inject other_evals_unchanged x_def x_in_oldM)
  qed
qed


lemma multiset_old_term_insert:
  assumes elem_group: "agg_key b cs elem = k"
  and old_term_eval: "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) \<noteq> {}"
  and old_val: "(meval_trm cs f elem, enat n) \<in> group_multiset k b cs f X" 
  and disjoint: "elem \<notin> X"
  and finite: "finite X"
  shows "group_multiset k b cs f (Set.insert elem X) = 
         Set.insert (meval_trm cs f elem, enat (n + 1)) ((group_multiset k b cs f X) - {(meval_trm cs f elem, enat n)})"
proof (rule set_eqI, rule iffI)
  fix x
  assume x_in_M: "x \<in> group_multiset k b cs f (Set.insert elem X)"
  then obtain t v where x_def: "x = (t, v)" by fastforce
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  define old_group where [simp]: "old_group = group k b cs X"
  define new_group where [simp]: "new_group = group k b cs updated_data"
  define old_evals where "old_evals = meval_trm cs f ` old_group"
  have group_ins: "new_group = Set.insert elem old_group" using elem_group by auto
  have y_card: "enat n = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) old_group)" using old_val by auto
  moreover have "Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) (Set.insert elem (Set.filter (\<lambda>x. agg_key b cs x = k) X)) =
                 Set.insert elem  (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) (Set.filter (\<lambda>x. agg_key b cs x = k) X))" by auto
  moreover have "elem \<notin> Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) (Set.filter (\<lambda>x. agg_key b cs x = k) X)" using disjoint by auto
  ultimately have correct_card: "enat (n + 1) = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) new_group)" 
    using eSuc_enat plus_1_eSuc(2) group_ins by(auto simp: ecard_def) (metis enat.distinct(2))
  then have aux1: "(meval_trm cs f elem, enat(n + 1)) \<in> group_multiset k b cs f (Set.insert elem X)" using group_ins
    by (auto simp del: Set.filter_eq)
  have aux2: "(meval_trm cs f elem, enat n) \<notin> group_multiset k b cs f (Set.insert elem X)" 
    using unique_term_multiset[OF aux1, of "enat n"] by simp
  show "x \<in> Set.insert (meval_trm cs f elem, enat (n + 1)) ((group_multiset k b cs f X) - {(meval_trm cs f elem, enat n)})"
  proof (cases "t = meval_trm cs f elem")
    case True
    then have "v = enat (n + 1)" using x_in_M x_def aux1 using unique_term_multiset by blast
    then show ?thesis using x_def x_in_M True by auto
  next
    case False
    then show ?thesis using other_evals_unchanged 
      by (metis DiffI elem_group insertI2 old.prod.inject singleton_iff x_def x_in_M)
  qed
next
  fix x
  assume x_in_oldM: "x \<in> Set.insert (meval_trm cs f elem, enat (n + 1)) ((group_multiset k b cs f X) - {(meval_trm cs f elem, enat n)})"
  then obtain t v where x_def: "x = (t, v)" by force
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  define old_group where [simp]: "old_group = group k b cs X"
  define new_group where [simp]: "new_group = group k b cs updated_data"
  define old_evals where "old_evals = meval_trm cs f ` old_group"
  have group_ins: "new_group = Set.insert elem old_group" using elem_group by auto
  have y_card: "enat n = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) old_group)" using old_val by auto
  moreover have "Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) (Set.insert elem (Set.filter (\<lambda>x. agg_key b cs x = k) X)) =
                 Set.insert elem  (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) (Set.filter (\<lambda>x. agg_key b cs x = k) X))" by auto
  moreover have "elem \<notin> Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) (Set.filter (\<lambda>x. agg_key b cs x = k) X)"
    using disjoint by auto
  ultimately have correct_card: "enat (n + 1) = ecard (Set.filter (\<lambda>xa. meval_trm cs f xa = meval_trm cs f elem) new_group)" 
    using eSuc_enat plus_1_eSuc(2) group_ins by(auto simp: ecard_def) (metis enat.distinct(2))
  then have aux1: "(meval_trm cs f elem, enat (n + 1)) \<in> group_multiset k b cs f (Set.insert elem X)" using group_ins by (auto simp del: Set.filter_eq)
  show "x \<in> group_multiset k b cs f (Set.insert elem X)" 
  proof (cases "t = meval_trm cs f elem")
    case True
    then have "v = enat (n + 1)" using x_in_oldM x_def by (metis DiffE insertE old.prod.inject old_val singleton_iff unique_term_multiset)
    then show ?thesis using True aux1 x_def by blast
  next
    case False
    then show ?thesis by (metis DiffD1 elem_group insertE old.prod.inject other_evals_unchanged x_def x_in_oldM)
  qed
qed

lemma length_flatten_multiset':
  assumes "finite X"
  shows "length (flatten_multiset(group_multiset k b cs f X)) = card (group k b cs X)"
  using assms
proof(induction X)
  case empty
  then have "group k b cs {} = {}" by auto
  then show ?case using length_flatten_multiset by auto
next
  case (insert elem F)
  define updated_data where [simp]: "updated_data = Set.insert elem F"
  define group where [simp]: "group = Set.filter (\<lambda>x. agg_key b cs x = k) updated_data"
  define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group"
  define old_group where [simp]: "old_group = Set.filter (\<lambda>x. agg_key b cs x = k) F"
  define old_M where [simp]: "old_M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) old_group))) ` meval_trm cs f ` old_group"
  define old_evals where "old_evals = meval_trm cs f ` old_group"
  interpret comp_fun_commute "\<lambda>(t, m) y. y + the_enat m" by unfold_locales auto
  have both_finite: "finite M \<and> finite old_M" using insert by auto
  show ?case
  proof(cases "agg_key b cs elem = k")
    case True
    then have group_elem: "agg_key b cs elem = k" by auto
    have "length(flatten_multiset(M)) = length(flatten_multiset(old_M)) + 1" 
    proof(cases "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) old_group = {}")
      case True
      then have "M = Set.insert (meval_trm cs f elem, 1) old_M" using multiset_new_term_insert True group_elem by simp
      moreover have "(meval_trm cs f elem, 1) \<notin> old_M" using True by auto
      ultimately show ?thesis using both_finite length_flatten_multiset by (simp add: enat_defs(2) length_flatten_multiset)
    next
      case False
      then obtain n where n_def: "(meval_trm cs f elem, enat n) \<in> old_M" 
        using valid_finite_group_mset[OF assms, of k b cs f] insert.hyps(1)
        by (force simp: ecard_def image_iff)
      then obtain xa where xa_def: "enat n = ecard (Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f xa) (Set.filter (\<lambda>x. agg_key b cs x = agg_key b cs xa) F))" 
        by auto
      have aux1: "finite (Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f xa) (Set.filter (\<lambda>x. agg_key b cs x = agg_key b cs xa) F))" using insert by auto
      have finite_remove: "finite (old_M - {(meval_trm cs f elem, enat n)})" using both_finite finite_Diff  by auto
      have finite_insert: "finite (Set.insert (meval_trm cs f elem, enat n) old_M)" using both_finite by blast
      have M_insert_remove_def: "M = Set.insert (meval_trm cs f elem, enat (n + 1)) (old_M - {(meval_trm cs f elem, enat n)})" 
        using multiset_old_term_insert group_elem False n_def insert
        by(simp only: M_def old_M_def group_def old_group_def updated_data_def group_multiset_def Let_def Optimized_Agg.group_def) auto
      then have aux: "length(flatten_multiset(Set.insert (meval_trm cs f elem, enat n) old_M)) = length(flatten_multiset(old_M - {(meval_trm cs f elem, enat n)})) + n" 
        using both_finite finite_insert finite_remove Finite_Set.comp_fun_commute_on.fold_insert_remove[of UNIV "\<lambda>(t, m) y. y + the_enat m" "(meval_trm cs f elem, enat n)" old_M 0]
        by (simp only: length_flatten_multiset) (metis case_prod_conv comp_fun_commute_on_axioms the_enat.simps top_greatest)
      have notin: "(meval_trm cs f elem, enat (n + 1)) \<notin> old_M - {(meval_trm cs f elem, enat n)}" using n_def old_M_def by force
      have old_len: "length (flatten_multiset old_M) = length (flatten_multiset (old_M - {(meval_trm cs f elem, enat n)})) + n"
        using aux by (simp only: insert_absorb[OF n_def])
      have "length (flatten_multiset M) = Finite_Set.fold (\<lambda>(t, m) y. y + the_enat m) 0 M"
        using both_finite by (simp only: length_flatten_multiset)
      also have "\<dots> = Finite_Set.fold (\<lambda>(t, m) y. y + the_enat m) 0 (old_M - {(meval_trm cs f elem, enat n)}) + (n + 1)"
        unfolding M_insert_remove_def fold_insert[OF finite_remove notin] by simp
      also have "\<dots> = length (flatten_multiset (old_M - {(meval_trm cs f elem, enat n)})) + (n + 1)"
        using finite_remove by (simp only: length_flatten_multiset)
      also have "\<dots> = length (flatten_multiset old_M) + 1"
        using old_len by linarith
      finally show ?thesis .
    qed
    moreover have "group = Set.insert elem old_group"
      using True insert by(auto) 
    ultimately show ?thesis using insert
      by (metis (no_types, lifting) ext M_def Optimized_Agg.group_def
          add.commute card_insert_disjoint finite_filter
          group_multiset_def insert_absorb local.group_def old_M_def
          old_group_def plus_1_eq_Suc updated_data_def)
  next
    case False
    then have aux: "Optimized_Agg.group k b cs (Set.insert elem F) = Optimized_Agg.group k b cs F" by auto
    then have "group_multiset k b cs f (Set.insert elem F) = group_multiset k b cs f F" by auto
    then show ?thesis using aux insert by auto
  qed
qed

lemma length_mset_eq:
  assumes "\<And> t m. ((t, m) \<in> s \<Longrightarrow> g t \<in> range Some)"
  and "valid_finite_mset s"
  shows "size (mset_conv g s) = length (flatten_multiset s)"
proof -
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)" 
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  interpret linorder "le_of_comp c" "lt_of_comp c"
    using ID_ccompare[OF c_def] .
  interpret comp_fun_commute "\<lambda>(t, m) y. y + the_enat m"
    by unfold_locales auto
  have "finite s" using assms(2) by (simp add:valid_finite_mset_def)
  then show ?thesis using assms(1-2) 
  proof(induction s)
    case empty
    then show ?case by(simp add:flatten_multiset_def csorted_list_of_set_def c_def mset_conv_def)
  next
    case (insert x F)
    then have *: "finite (Set.insert x F)" by auto
    have length_eq: "length (flatten_multiset F) = size (mset_conv g F)" using insert by(auto) (metis insertI2 valid_finite_mset_def)
    obtain t i where [simp]: "x = (t, enat i)" using insert(5) by(simp add:valid_finite_mset_def) (metis surj_pair) 
    then obtain k where "g t = Some k" using insert(4) by auto
    then show ?case using length_flatten_multiset[OF *] fold_insert[OF insert(1-2)] length_eq 
      Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of g] _ insert(1-2)] 
      length_flatten_multiset[OF insert(1)] by(simp add:mset_conv_def)
  qed
qed

lemma valid_insert_sum_unfolded:
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (SumAux m) X" 
  and disjoint: "elem \<notin> X"
  shows "let (v', m') = insert_sum \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> elem (v, m) in
      if v' then valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (SumAux m') (X \<union> {elem})
      else True"
proof - 
  let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
  let ?new_data = "(X \<union> {elem})"
  obtain v' m' where ins_def: "(v', m') = insert_sum ?args elem (v, m)" by (metis surj_pair)
  interpret comp_fun_commute "((+)::(integer \<Rightarrow> integer \<Rightarrow> integer))"  
    by unfold_locales auto
  show ?thesis
  proof(cases v')
    case True
    then have valid: "v = True" using ins_def by auto (metis Pair_inject)
    then obtain i where i_def: "meval_trm cs f elem = EInt i" using True ins_def by(auto split:event_data.splits option.splits)
    then have new_map_def: "m' = Mapping.update (agg_key (length tys) cs elem) (case Mapping.lookup m (agg_key (length tys) cs elem) of
                         Some (c, s) \<Rightarrow> (c + 1, s + i) |
                         None \<Rightarrow> (1, i)) m"
      using ins_def valid i_def by(auto cong:option.case_cong split:option.splits)
    have finite_X: "finite X" using valid valid_before by auto
    then have valid_finite: "finite ?new_data" by auto
    have valid_aggtype: "fst \<omega> = Formula.Agg_Sum \<or> fst \<omega> = Formula.Agg_Avg" using valid_before valid by auto
    have valid_type_restr: "type_restr ?args (Set.insert elem X)" using valid_before valid i_def by(auto simp:type_restr_def)
    have valid_key_invariant: "\<And>k. k \<in> (agg_key (length tys) cs) ` ?new_data \<longleftrightarrow> k \<in> Mapping.keys m'"
      using valid_before valid new_map_def by simp
    have valid_value_invariant: "\<And>k. k \<in> Mapping.keys m' \<longrightarrow> Mapping.lookup m' k = 
          (let group = Set.filter (\<lambda>x. agg_key (length tys) cs x = k) ?new_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
          in Some (size (int_mset_conv M), fold_mset (+) 0 (int_mset_conv M)))"
    proof rule
      fix k
      assume k_in: "k \<in> Mapping.keys m'"
      let ?M = "group_multiset k (length tys) cs f ?new_data"
      let ?old_M = "group_multiset k (length tys) cs f X"
      have "(meval_trm cs f) ` ?new_data \<subseteq> range EInt" using valid_before valid i_def
        by(auto simp:type_restr_def image_subset_iff)
      then have "(\<And>t m. (t, m) \<in> (group_multiset k (length tys) cs f ?new_data) \<Longrightarrow> t \<in> range EInt)" by fastforce
      then have type_restr: "set (flatten_multiset (group_multiset k (length tys) cs f ?new_data)) \<subseteq> range EInt"
        using flatten_multiset_range[of _ EInt] valid_finite by auto
      have finite_old_M: "finite ?old_M" using finite_filter finite_imageI valid_finite by auto
      show "Mapping.lookup m' k = 
          (let group = Set.filter (\<lambda>x. agg_key (length tys) cs x = k) ?new_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
          in Some (size (int_mset_conv M), fold_mset (+) 0 (int_mset_conv M)))"
      proof(cases "agg_key (length tys) cs elem = k")
        case True
        then have k_def: "agg_key (length tys) cs elem = k" by auto 
        show ?thesis
        proof(cases "Mapping.lookup m k")
          case None
          then have *: "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k (length tys) cs X) = {}" "?old_M = {}"
            using valid_before valid by(auto) (metis domIff keys_dom_lookup rev_image_eqI)+
          have M_single: "?M = Set.insert (meval_trm cs f elem, enat 1) {}"
            using multiset_new_term_insert[OF True *(1)] *(2) by (simp add: one_enat_def del: Set.filter_eq)
          then have valid_size: "size (int_mset_conv ?M) = 1"
            using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int]] i_def
            by(simp add:int_mset_conv_def mset_conv_def unpack_int_def)
          then have valid_fold: "fold_mset (+) 0 (int_mset_conv ?M) = i"
            using M_single Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int]] i_def
            by(simp add:int_mset_conv_def mset_conv_def unpack_int_def)
          then show ?thesis using valid_size valid_fold new_map_def None True lookup_update'[of _ _ m] by simp
        next
          case (Some a)
          then obtain len sum where [simp]: "a = (len, sum)" by (meson surj_pair)
          have k_in_old: "k \<in> Mapping.keys m" using Some by (simp add: keys_is_none_rep)
          have a_def: "len = size (int_mset_conv ?old_M)" "sum = fold_mset (+) 0 (int_mset_conv ?old_M)" 
            using valid valid_before Some new_map_def k_in_old by auto
          then show ?thesis 
          proof(cases "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k (length tys) cs X) = {}")
            case True
            then have not_in: "(meval_trm cs f elem, 1) \<notin> ?old_M" by auto
            have M_def: "?M = Set.insert (meval_trm cs f elem, 1) ?old_M" 
              using multiset_new_term_insert[OF k_def True] by simp
            then have valid_size: "size (int_mset_conv ?M) = len + 1"
              using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ finite_old_M not_in] i_def a_def(1)
              by(simp add:int_mset_conv_def mset_conv_def unpack_int_def one_enat_def)
            have valid_fold: "fold_mset (+) 0 (int_mset_conv ?M) = sum + i"
              using M_def Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ finite_old_M not_in] i_def a_def(2)
              by(simp add:int_mset_conv_def mset_conv_def unpack_int_def one_enat_def)
            show ?thesis using valid_size valid_fold new_map_def Some by (simp add: k_def)
          next
            case False
            then obtain n where n_def: "(meval_trm cs f elem, enat n) \<in> ?old_M" 
              using valid_finite_group_mset[of X k "length tys" cs f] k_def finite_X
              by (fastforce simp add:valid_finite_mset_def image_iff)
            then have not_in: "(meval_trm cs f elem, enat (n + 1)) \<notin> ?old_M" using unique_term_multiset[OF n_def] by auto
            have valid_unpack: "unpack_int (meval_trm cs f elem) \<in> range Some" using i_def by(simp add: unpack_int_def)
            have M_insert_remove_def: "?M = Set.insert (meval_trm cs f elem, enat (n + 1)) (?old_M - {(meval_trm cs f elem, enat n)})" 
              using multiset_old_term_insert[OF k_def False n_def disjoint finite_X] by simp
            then have mset_conv_eq: "int_mset_conv ?M = add_mset i (int_mset_conv ?old_M)" 
              using mset_conv_insert_remove[OF n_def _ not_in finite_old_M, of unpack_int] valid_unpack i_def
              by(simp add:int_mset_conv_def unpack_int_def)
            have valid_size: "size (int_mset_conv ?M) = len + 1"
              using mset_conv_eq Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ finite_old_M not_in] i_def a_def(1)
              by(simp add:int_mset_conv_def mset_conv_def unpack_int_def one_enat_def)
            moreover have valid_fold: "fold_mset (+) 0 (int_mset_conv ?M) = sum + i"
              using mset_conv_eq Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ finite_old_M not_in] i_def a_def(2)
              by(simp add:int_mset_conv_def mset_conv_def unpack_int_def one_enat_def)
            ultimately show ?thesis using valid_size valid_fold new_map_def Some by (simp add: k_def)
          qed
        qed
      next
        case False
        then show ?thesis using new_map_def lookup_update'[of _ _ m] valid_before 
            valid k_in filter_insert[of "(\<lambda>x. agg_key (length tys) cs x = k)"] by(auto split:option.splits)
      qed
    qed
    have "valid_maggaux ?args (SumAux m') (X \<union> {elem})" 
      using valid_finite valid_aggtype valid_type_restr valid_key_invariant valid_value_invariant by auto
    then show ?thesis using ins_def  by(simp only:Let_def) fastforce  
  next
    case False
    then show ?thesis using ins_def[symmetric] by simp
  qed
qed

lemma valid_insert_cnt_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (CntAux m) X" 
  and disjoint: "elem \<notin> X"
  shows "let (v', m') = insert_cnt \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> elem (v, m) in
      if v' then valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (CntAux m') (X \<union> {elem}) 
      else True"
proof - 
  let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
  let ?new_data = "(X \<union> {elem})"
  obtain v' m' where ins_def: "(v', m') = insert_cnt ?args elem (v, m)" by (metis insert_cnt.simps(1))
  show ?thesis
  proof(cases v')
    case True
    then have valid: "v = True" using ins_def by (auto split:if_splits)
    have new_map_def: "m' = Mapping.update (agg_key (length tys) cs elem) (case Mapping.lookup m (agg_key (length tys) cs elem) of 
                                 Some i \<Rightarrow> (i + 1) |
                                 None \<Rightarrow>  1) m"
      using ins_def valid by (auto split:option.splits)
    have finite_X: "finite X" using valid valid_before by auto
    then have valid_finite: "finite ?new_data" by auto
    have valid_aggtype: "fst \<omega> = Formula.Agg_Cnt" using valid_before valid by auto
    have valid_type_restr: "type_restr ?args (Set.insert elem X)" using valid_before valid  by(auto simp:type_restr_def)
    have valid_key_invariant: "\<And>k. k \<in> (agg_key (length tys) cs) ` ?new_data \<longleftrightarrow> k \<in> Mapping.keys m'"
      using valid_before valid new_map_def by simp
  have valid_value_invariant: "\<And>k. k \<in> Mapping.keys m' \<longrightarrow> Mapping.lookup m' k = 
          (let group = Set.filter (\<lambda>x. agg_key (length tys) cs x = k) ?new_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
          in Some (size (mset_conv Some M)))"
  proof rule
    fix k
    assume k_in: "k \<in> Mapping.keys m'"
    let ?M = "group_multiset k (length tys) cs f ?new_data"
    let ?old_M = "group_multiset k (length tys) cs f X"
    have finite_old_M: "finite ?old_M" using finite_filter finite_imageI valid_finite by auto
    show "Mapping.lookup m' k = 
          (let group = Set.filter (\<lambda>x. agg_key (length tys) cs x = k) ?new_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
          in Some (size (mset_conv Some M)))"
    proof(cases "agg_key (length tys) cs elem = k")
      case True
      then have k_def: "agg_key (length tys) cs elem = k" by auto 
      then show ?thesis
      proof(cases "Mapping.lookup m k")
        case None
        then have *: "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k (length tys) cs X) = {}" "?old_M = {}"
          using valid_before valid by(auto) (metis domIff keys_dom_lookup rev_image_eqI)+
        have M_single: "?M = Set.insert (meval_trm cs f elem, enat 1) {}"
          using multiset_new_term_insert[OF True *(1)] *(2) by (simp add: one_enat_def del: Set.filter_eq)
        then have valid_size: "size (mset_conv Some ?M) = 1"
          using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of Some], of  "(meval_trm cs f elem, enat 1)"]
          by(simp add:mset_conv_def)
        then show ?thesis using valid_size new_map_def None True lookup_update'[of _ _ m] by simp
      next
        case (Some a)
        have k_in_old: "k \<in> Mapping.keys m" using Some by (simp add: keys_is_none_rep)
        have a_def: "a = size (mset_conv Some ?old_M)"
          using valid valid_before Some new_map_def k_in_old by auto
        then show ?thesis 
        proof(cases "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k (length tys) cs X) = {}")
          case True
          then have not_in: "(meval_trm cs f elem, 1) \<notin> ?old_M" by auto
          have M_def: "?M = Set.insert (meval_trm cs f elem, 1) ?old_M" 
            using multiset_new_term_insert[OF k_def True] by simp
          then have valid_size: "size (mset_conv Some ?M) = a + 1"
            using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of Some] _ finite_old_M not_in] a_def
            by(simp add: mset_conv_def one_enat_def)
          then show ?thesis using new_map_def Some by (simp add: k_def)
        next
          case False
          then obtain n where n_def: "(meval_trm cs f elem, enat n) \<in> ?old_M" 
            using valid_finite_group_mset[of X k "length tys" cs f] k_def finite_X by(fastforce simp add:valid_finite_mset_def image_iff)
          then have not_in: "(meval_trm cs f elem, enat (n + 1)) \<notin> ?old_M" using unique_term_multiset[OF n_def] by auto
          have M_insert_remove_def: "?M = Set.insert (meval_trm cs f elem, enat (n + 1)) (?old_M - {(meval_trm cs f elem, enat n)})" 
            using multiset_old_term_insert[OF k_def False n_def disjoint finite_X] by simp
          then have mset_conv_eq: "mset_conv Some ?M = add_mset (meval_trm cs f elem) (mset_conv Some ?old_M)" 
            using mset_conv_insert_remove[OF n_def _ not_in finite_old_M, of Some]
            by simp
          have valid_size: "size (mset_conv Some ?M) = a + 1"
            using mset_conv_eq Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of Some] _ finite_old_M not_in] a_def
            by(simp add:mset_conv_def one_enat_def)
          then show ?thesis using new_map_def Some by (simp add: k_def)
        qed
      qed
    next
      case False
      then show ?thesis using new_map_def lookup_update'[of _ _ m] valid_before 
            valid k_in filter_insert[of "(\<lambda>x. agg_key (length tys) cs x = k)"] by(auto split:option.splits)
      qed
    qed
    have "valid_maggaux ?args (CntAux m') (X \<union> {elem})" 
      using valid_finite valid_aggtype valid_type_restr valid_key_invariant valid_value_invariant by auto
    then show ?thesis using ins_def by(simp only:Let_def) fastforce
  next
    case False
    then show ?thesis using ins_def[symmetric] by simp
  qed
qed

lemma valid_insert_rank_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (RankAux (m, type)) X" 
  and disjoint: "elem \<notin> X"
  shows "let (v', m') = insert_rank \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> type elem (v, m) in
      if v' then valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (RankAux (m', type)) (X \<union> {elem})
      else True"
proof - 
  let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
  let ?new_data = "Set.insert elem X"
  obtain v' m' where ins_def: "(v', m') = insert_rank ?args type elem (v, m)" using prod.collapse by blast
  show ?thesis
  proof(cases v')
    case True
    then have valid: "v = True" using ins_def by auto (metis Pair_inject)
    have valid_new: "v' = True" using True by simp
    obtain i s where meval_def: "meval_trm cs f elem = EInt i \<or> meval_trm cs f elem = EString s" 
      using valid True ins_def by(auto split:event_data.splits option.splits list_aux.splits)
    then have new_map_def: "m' = Mapping.update (agg_key (length tys) cs elem) (case (Mapping.lookup m (agg_key (length tys) cs elem), meval_trm cs f elem) of
                              (Some (LInt t'), EInt term') \<Rightarrow> LInt (insert_treelist term' t') |
                              (Some (LString t'), EString term') \<Rightarrow> LString (insert_treelist term' t') |
                              (None, EInt term') \<Rightarrow> LInt (insert_treelist term' empty_treelist) |
                              (None, EString term') \<Rightarrow> LString (insert_treelist term' empty_treelist)) m"
      using ins_def valid meval_def True by(auto split:event_data.splits option.splits list_aux.splits type.splits)
    have finite_X: "finite X" using valid valid_before by auto
    then have valid_finite: "finite ?new_data" by auto
    have valid_aggtype: "fst \<omega> = Formula.Agg_Min \<or> fst \<omega> = Formula.Agg_Max \<or> fst \<omega> = Formula.Agg_Med" using valid_before valid by auto
    have y0_restr: "type = StringT \<longleftrightarrow> (meval_trm cs f elem) \<in> range EString" 
      using valid valid_before True ins_def by(auto split:event_data.splits list_aux.splits option.splits type.splits)
    have valid_type_restr: "(case type of IntT \<Rightarrow> (meval_trm cs f ` (Set.insert elem X)) \<subseteq> range EInt | 
                                 StringT \<Rightarrow> (meval_trm cs f ` (Set.insert elem X)) \<subseteq> range EString)" using valid_before valid meval_def y0_restr 
      by(auto split:type.splits)
    have valid_key_invariant: "\<And>k. k \<in> (agg_key (length tys) cs) ` ?new_data \<longleftrightarrow> k \<in> Mapping.keys m'"
      using valid_before valid new_map_def by simp
    have valid_value_invariant: 
    "\<And>k. k \<in> Mapping.keys m' \<longrightarrow> (case Mapping.lookup m' k of
      Some t \<Rightarrow> (let group = Set.filter (\<lambda>x. agg_key (length tys) cs x = k) ?new_data;
                 M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
                 in valid_list_aux t M type) |
      None \<Rightarrow> False)" 
    proof rule
      fix k
      let ?M = "group_multiset k (length tys) cs f ?new_data"
      let ?old_M = "group_multiset k (length tys) cs f X"
      have finite_old_M: "finite ?old_M" using finite_filter finite_imageI valid_finite by auto
      assume k_in: "k \<in> Mapping.keys m'"
      show "(case Mapping.lookup m' k of
      Some t \<Rightarrow> (let group = Set.filter (\<lambda>x. agg_key (length tys) cs x = k) ?new_data;
                 M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
                 in valid_list_aux t M type) |
      None \<Rightarrow> False)"
      proof(cases "agg_key (length tys) cs elem = k")
        case True 
        then have k_def: "agg_key (length tys) cs elem = k" by auto
        have the_enat_one: "the_enat 1 = 1" by (simp add: replicate_mset_def one_enat_def)  
        have list_elem_restr: "\<forall>l. Mapping.lookup m k = Some (LInt l) \<longrightarrow> meval_trm cs f elem \<in> range EInt"
                              "\<forall>l. Mapping.lookup m k = Some (LString l) \<longrightarrow> meval_trm cs f elem \<in> range EString"
        using True ins_def valid valid_new k_def by(auto split:event_data.splits option.splits)
        then show ?thesis
        proof(cases "Mapping.lookup m k")
          case None
          then have *: "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k (length tys) cs X) = {}" "?old_M = {}"
            using valid_before valid by(auto) (metis domIff keys_dom_lookup rev_image_eqI)+
          have "?M = Set.insert (meval_trm cs f elem, 1) {}" using multiset_new_term_insert[OF k_def *(1)] *(2) by auto
          then show ?thesis using None k_in new_map_def meval_def mset_treelist_insert[of s empty_treelist] mset_treelist_insert[of i empty_treelist]
            Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int]] y0_restr
            Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_string]]
            by(auto simp:mset_treelist_empty k_def valid_list_aux_def valid_list_aux'_def int_mset_conv_def 
                  unpack_int_def the_enat_one type_restr_mset_def str_mset_conv_def unpack_string_def type_restr_def mset_conv_def
                  split:event_data.splits list_aux.splits type.splits)
        next
          case (Some a)
          have k_in_old: "k \<in> Mapping.keys m" using Some by (simp add: keys_is_none_rep)
          have valid_old: "valid_list_aux a ?old_M type" using valid_before valid Some k_in_old by auto
          show ?thesis 
          proof(cases "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k (length tys) cs X) = {}")
            case True
            have not_in: "(meval_trm cs f elem, 1) \<notin> ?old_M" using True by auto
            have mset_rel: "?M = Set.insert (meval_trm cs f elem, 1) ?old_M"
              using multiset_new_term_insert[OF k_def True] by auto
            show ?thesis
            proof (cases "meval_trm cs f elem")
              case (EInt j)
              then obtain l where a_def: "a = LInt l"
                using list_elem_restr(2) Some by (cases a) auto
              have "int_mset_conv ?M = add_mset j (int_mset_conv ?old_M)"
                using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ finite_old_M not_in]
                unfolding mset_rel by (simp add: EInt int_mset_conv_def mset_conv_def unpack_int_def the_enat_one)
              moreover have "type_restr_mset EInt ?M"
                using valid_old unfolding mset_rel by (auto simp: a_def EInt valid_list_aux_def type_restr_mset_def)
              moreover have "Mapping.lookup m' k = Some (LInt (insert_treelist j l))"
                using Some by (simp add: new_map_def k_def a_def EInt lookup_update')
              ultimately show ?thesis
                using valid_old mset_treelist_insert[of j l]
                by (simp add: a_def valid_list_aux_def valid_list_aux'_def)
            next
              case (EString j)
              then obtain l where a_def: "a = LString l"
                using list_elem_restr(1) Some by (cases a) auto
              have "str_mset_conv ?M = add_mset j (str_mset_conv ?old_M)"
                using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_string] _ finite_old_M not_in]
                unfolding mset_rel by (simp add: EString str_mset_conv_def mset_conv_def unpack_string_def the_enat_one)
              moreover have "type_restr_mset EString ?M"
                using valid_old unfolding mset_rel by (auto simp: a_def EString valid_list_aux_def type_restr_mset_def)
              moreover have "Mapping.lookup m' k = Some (LString (insert_treelist j l))"
                using Some by (simp add: new_map_def k_def a_def EString lookup_update')
              ultimately show ?thesis
                using valid_old mset_treelist_insert[of j l]
                by (simp add: a_def valid_list_aux_def valid_list_aux'_def)
            next
              case (EFloat x)
              then show ?thesis using meval_def by simp
            qed
          next
            case False
            then obtain n where n_def: "(meval_trm cs f elem, enat n) \<in> ?old_M" 
              using valid_finite_group_mset[of X k "length tys" cs f] k_def finite_X by(fastforce simp add:valid_finite_mset_def image_iff)
            then have not_in: "(meval_trm cs f elem, enat (n + 1)) \<notin> ?old_M" using unique_term_multiset[OF n_def] by auto
            have M_insert_remove_def: "?M = Set.insert (meval_trm cs f elem, enat (n + 1)) (?old_M - {(meval_trm cs f elem, enat n)})" 
              using multiset_old_term_insert[OF k_def False n_def disjoint finite_X] by simp
            then show ?thesis
            proof (cases "meval_trm cs f elem")
              case (EInt x1)
              then obtain l where a_def: "a = LInt l"
                using list_elem_restr(2) Some by (cases a) auto
              have "int_mset_conv ?M = add_mset x1 (int_mset_conv ?old_M)" 
                using EInt M_insert_remove_def mset_conv_insert_remove[OF n_def _ not_in finite_old_M, of unpack_int]
                by(simp add:int_mset_conv_def unpack_int_def)
              moreover have "type_restr_mset EInt ?M"
              proof -
                have "type_restr_mset EInt ?old_M"
                  using valid_old by (simp add: a_def valid_list_aux_def)
                then show ?thesis
                  using EInt unfolding M_insert_remove_def type_restr_mset_def by blast
              qed
              moreover have "Mapping.lookup m' k = Some (LInt (insert_treelist x1 l))"
                using Some by (simp add: new_map_def k_def a_def EInt lookup_update')
              ultimately show ?thesis
                using valid_old mset_treelist_insert[of x1 l]
                by (simp add: a_def valid_list_aux_def valid_list_aux'_def)
            next
              case (EFloat x2)
              then show ?thesis using meval_def by auto
            next
              case (EString x3)
              then obtain l where a_def: "a = LString l"
                using list_elem_restr(1) Some by (cases a) auto
              have "str_mset_conv ?M = add_mset x3 (str_mset_conv ?old_M)" 
                using EString M_insert_remove_def mset_conv_insert_remove[OF n_def _ not_in finite_old_M, of unpack_string]
                by(simp add:str_mset_conv_def unpack_string_def)
              moreover have "type_restr_mset EString ?M"
              proof -
                have "type_restr_mset EString ?old_M"
                  using valid_old by (simp add: a_def valid_list_aux_def)
                then show ?thesis
                  using EString unfolding M_insert_remove_def type_restr_mset_def by blast
              qed
              moreover have "Mapping.lookup m' k = Some (LString (insert_treelist x3 l))"
                using Some by (simp add: new_map_def k_def a_def EString lookup_update')
              ultimately show ?thesis
                using valid_old mset_treelist_insert[of x3 l]
                by (simp add: a_def valid_list_aux_def valid_list_aux'_def)
            qed
          qed
        qed
      next
        case False
        then show ?thesis using new_map_def lookup_update'[of _ _ m] valid_before 
            valid k_in filter_insert[of "(\<lambda>x. agg_key (length tys) cs x = k)"] by(auto split:option.splits)
      qed
    qed
    have "valid_maggaux ?args (RankAux (m', type)) (X \<union> {elem})" 
      using valid_finite valid_aggtype valid_type_restr valid_key_invariant valid_value_invariant
      by(simp cong:option.case_cong)
    then show ?thesis using ins_def by(simp only:Let_def) force
  next
    case False
    then show ?thesis using ins_def[symmetric] by simp
  qed
qed

lemma valid_insert_maggaux_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> aux X"
  and finite: "finite Y"
  and disjoint: "X \<inter> Y = {}"
shows "let (v', aux') = insert_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> Y aux in
  if v' then valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> aux' (X \<union> Y)
  else True" 
  using assms(1)
proof -
  have finite_X: "finite X" using valid_before by(auto)
  show ?thesis using valid_before
  proof(induction aux)
    case (CntAux m)
    show ?case using finite disjoint CntAux
    proof(induction Y)
      case empty
      then show ?case by auto
    next
      case (insert x F)
      let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
      interpret comp_fun_commute "insert_cnt ?args"
        using insert_cnt_comm by unfold_locales auto
      obtain v' m' where intermediate_map_def: "(v', CntAux m') = insert_maggaux ?args F (CntAux m)" 
        by (cases "Finite_Set.fold (insert_cnt ?args) (True, m) F") auto
      then have fold_def: "Finite_Set.fold (insert_cnt ?args) (True, m) F = (v', m')" 
        by(auto split:prod.splits)
      obtain v_f m_f where final_map_def: "(v_f, m_f) = insert_cnt ?args x (v', m')" by auto metis
      show ?case
      proof (cases v_f)
        case True 
        have disj: "X \<inter> F = {}" using insert(4) by blast
        have not_in: "x \<notin> X \<union> F" using insert(2) insert(4) by force
        have int_true: "v' = True" using True final_map_def by auto (metis Pair_inject)
        then have valid_inter: "valid_maggaux ?args (CntAux m') (X \<union> F)" 
          using insert(3)[OF disj CntAux] fold_def by(simp add:intermediate_map_def split:prod.splits)
        have "valid_maggaux ?args (CntAux m_f) (X \<union> F \<union> {x})"
          using valid_insert_cnt_unfolded[OF valid_inter not_in, of v'] final_map_def True int_true by simp
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def 
          by(simp del:insert_cnt.simps split:prod.splits) force
      next
        case False
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def 
          by(simp del:insert_cnt.simps valid_maggaux.simps split:prod.splits) force
      qed
    qed
  next
    case (SumAux m)
    show ?case using finite disjoint SumAux
    proof(induction Y)
      case empty
      then show ?case by auto 
    next
      case (insert x F)
      let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
      interpret comp_fun_commute "insert_sum ?args"
        using insert_sum_comm by unfold_locales auto
      obtain v' m' where intermediate_map_def: "(v', SumAux m') = insert_maggaux ?args F (SumAux m)" 
        by (cases "Finite_Set.fold (insert_sum ?args) (True, m) F") auto
      then have fold_def: "Finite_Set.fold (insert_sum ?args) (True, m) F = (v', m')" 
        by(auto split:prod.splits)
      obtain v_f m_f where final_map_def: "(v_f, m_f) = insert_sum ?args x (v', m')" using prod.collapse by blast
     show ?case
      proof (cases v_f)
        case True 
        have disj: "X \<inter> F = {}" using insert(4) by blast
        have not_in: "x \<notin> X \<union> F" using insert(2) insert(4) by force
        have int_true: "v' = True" using True final_map_def by auto (metis Pair_inject)
        then have valid_inter: "valid_maggaux ?args (SumAux m') (X \<union> F)" 
          using insert(3)[OF disj SumAux] fold_def by(simp add:intermediate_map_def split:prod.splits)
        have "valid_maggaux ?args (SumAux m_f) (X \<union> F \<union> {x})"
          using valid_insert_sum_unfolded[OF valid_inter not_in, of v'] final_map_def True int_true 
          by (simp split:prod.splits)
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def 
          by(simp del:insert_cnt.simps split:prod.splits) force
      next
        case False
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def 
          by(simp del:insert_sum.simps valid_maggaux.simps split:prod.splits) force
      qed
    qed
  next
    case (RankAux aux)
    then obtain m type where [simp]: "aux = (m, type)" by (meson surj_pair)
    show ?case using finite disjoint RankAux
    proof(induction Y)
      case empty
      then show ?case by auto 
    next
      case (insert x F)
      let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
      interpret comp_fun_commute "insert_rank ?args type"
        using insert_rank_comm by unfold_locales auto
      obtain v' m' where intermediate_map_def: "(v', RankAux (m', type)) = insert_maggaux ?args F (RankAux aux)" 
        by (cases "Finite_Set.fold (insert_rank ?args type) (True, m) F") auto
      then have fold_def: "Finite_Set.fold (insert_rank ?args type) (True, m) F = (v', m')" 
        by(auto split:prod.splits)
      obtain v_f m_f where final_map_def: "(v_f, m_f) = insert_rank ?args type x (v', m')" using prod.collapse by blast
      show ?case
      proof (cases v_f)
        case True 
        have disj: "X \<inter> F = {}" using insert(4) by blast
        have not_in: "x \<notin> X \<union> F" using insert(2) insert(4) by force
        have int_true: "v' = True" using True final_map_def by auto (metis Pair_inject)
        then have valid_inter: "valid_maggaux ?args (RankAux (m', type)) (X \<union> F)" 
          using insert(3)[OF disj RankAux] fold_def by(simp add:intermediate_map_def split:prod.splits)
        have "valid_maggaux ?args (RankAux (m_f, type)) (X \<union> F \<union> {x})"
          using valid_insert_rank_unfolded[OF valid_inter not_in, of v'] final_map_def True int_true 
          by (simp split:prod.splits)
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def 
          by(simp del:insert_rank.simps split:prod.splits) force
      next
        case False
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def 
          by(simp del:insert_rank.simps valid_maggaux.simps split:prod.splits) force
      qed
    qed
  qed
qed

lemma valid_insert_maggaux: "valid_maggaux args aux X \<Longrightarrow> finite Y \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow> 
  let (v', aux') = insert_maggaux args Y aux in if v' then valid_maggaux args aux' (X \<union> Y) else True"
  using valid_insert_maggaux_unfolded by(cases args) blast


lemma valid_delete_sum_unfolded:
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (SumAux m) X" 
  and in_set: "elem \<in> X"
  shows "let (v', m') = delete_sum \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> elem (v, m) in
      if v' then valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (SumAux m') (X - {elem})
      else True"
proof - 
  let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
  let ?new_data = "(X - {elem})"
  interpret comp_fun_commute "((+)::(integer \<Rightarrow> integer \<Rightarrow> integer))"  
    by unfold_locales auto
  define b where "b = length tys"
  obtain v' m' where del_def: "(v', m') = delete_sum ?args elem (v, m)" by (metis surj_pair)
  show ?thesis
  proof(cases v')
    case True
    then have valid: "v = True" using del_def by (auto split:if_splits)
    have finite_X: "finite X" using valid valid_before by auto
    then have valid_finite: "finite ?new_data" by auto
    have elem_in: "agg_key b cs elem \<in> Mapping.keys m" using b_def in_set valid valid_before by auto
    have all_int: "meval_trm cs f ` X \<subseteq> range EInt" using valid valid_before by(auto simp:type_restr_def) blast+
    then have valid_unpack: "(\<And>t m. (t, m) \<in> group_multiset (agg_key b cs elem) b cs f X \<Longrightarrow> unpack_int t \<in> range Some)"
      by(auto simp:unpack_int_def split:event_data.splits)
    obtain c s where lookup_def: "Mapping.lookup m (agg_key b cs elem) = Some (c, s)" using b_def True del_def valid by(auto split:option.splits)
    then have "c = length (flatten_multiset (group_multiset (agg_key b cs elem) b cs f X))" 
      using length_mset_eq[OF _ valid_finite_group_mset[OF finite_X, of "(agg_key b cs elem)" b cs f], of unpack_int] valid_unpack
      valid valid_before elem_in b_def by(simp add:int_mset_conv_def) 
    then have c_def: "c = card(group (agg_key b cs elem) b cs X)" using finite_X length_flatten_multiset' by blast
    obtain i where i_def: "meval_trm cs f elem = EInt i" using True valid del_def lookup_def b_def by(auto split:event_data.splits)
    have new_map_def: "m' = (if c = 1 then Mapping.delete (agg_key b cs elem) m else Mapping.update (agg_key b cs elem) (c - 1, s - i) m)"
      using del_def valid lookup_def i_def b_def by simp
    have valid_aggtype: "fst \<omega> = Formula.Agg_Sum \<or> fst \<omega> = Formula.Agg_Avg" using valid_before valid by auto
    have valid_type_restr: "type_restr ?args (X - {elem})" using valid_before valid by(auto simp:type_restr_def) blast+
    have valid_key_invariant: "\<And>k. k \<in> (agg_key b cs) ` ?new_data \<longleftrightarrow> k \<in> Mapping.keys m'"
    proof (rule iffI)
      fix k
      assume assm: "k \<in> agg_key b cs ` (X - {elem})"
      show "k \<in> Mapping.keys m'" 
      proof(cases "agg_key b cs elem = k")
        case True
        from assm obtain e where e: "e \<in> X" "e \<noteq> elem" "agg_key b cs e = k" by auto
        have "c \<noteq> 1"
        proof
          assume "c = 1"
          then obtain z where "group (agg_key b cs elem) b cs X = {z}"
            unfolding c_def by (rule card_1_singletonE)
          moreover have "elem \<in> group (agg_key b cs elem) b cs X" "e \<in> group (agg_key b cs elem) b cs X"
            using in_set e True by auto
          ultimately show False using e(2) by (metis singletonD)
        qed
        then show ?thesis using True new_map_def by simp
      next
        case False
        then have "k \<in> (agg_key b cs) ` X" using assm valid_before by auto
        then have "k \<in> Mapping.keys m" using valid_before valid b_def by auto
        then show ?thesis using False new_map_def by auto
      qed
    next
      fix k
      assume assm: "k \<in> Mapping.keys m'" 
      then have in_map: "k \<in> Mapping.keys m" using new_map_def elem_in by(auto split:if_splits) 
      then have in_set: "k \<in> (agg_key b cs) ` X" using valid_before valid b_def by auto
      show "k \<in> (agg_key b cs) ` (X - {elem})"
      proof(cases "agg_key b cs elem = k")
        case True
        then have not_1: "c \<noteq> 1" using assm new_map_def by(auto split:option.splits)
        then have "card (group k b cs X) \<noteq> 1" using c_def True by(auto)
        moreover have "group k b cs X \<noteq> {}" using True assms by auto
        ultimately obtain k' where "k' \<in> group k b cs X" "k' \<noteq> elem" by (metis is_singletonI' is_singleton_altdef)
        then show ?thesis by auto
      next
        case False
        then show ?thesis using in_set by auto
      qed
    qed
    have valid_value_invariant: "\<And>k. k \<in> Mapping.keys m' \<longrightarrow> Mapping.lookup m' k = 
          (let group = Set.filter (\<lambda>x. agg_key b cs x = k) ?new_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
          in Some (size (int_mset_conv M), fold_mset (+) 0 (int_mset_conv M)))"
    proof rule
      fix k
      assume k_in: "k \<in> Mapping.keys m'"
      let ?M = "group_multiset k b cs f ?new_data"
      let ?old_M = "group_multiset k b cs f X"
      obtain len sum where *: "Mapping.lookup m k = Some (len, sum)" using k_in by (metis Optimized_Agg.lookup_delete elem_in insert_absorb is_none_simps(1) keys_is_none_rep keys_update new_map_def not_None_eq prod.exhaust_sel)
      then have k_in_old: "k \<in> Mapping.keys m" by (simp add: keys_is_none_rep)
      then have vals: "len = size (int_mset_conv ?old_M)" "sum = fold_mset (+) 0 (int_mset_conv ?old_M)" using valid valid_before * k_in_old b_def by auto
      have "(meval_trm cs f) ` ?new_data \<subseteq> range EInt" using valid_before valid i_def
        by(auto simp:type_restr_def image_subset_iff)
      then have "(\<And>t m. (t, m) \<in> (group_multiset k b cs f ?new_data) \<Longrightarrow> t \<in> range EInt)" by fastforce
      then have type_restr: "set (flatten_multiset (group_multiset k b cs f ?new_data)) \<subseteq> range EInt"
        using flatten_multiset_range[of _ EInt] valid_finite by auto
      have finite_old_M: "finite ?old_M" using finite_filter finite_imageI valid_finite by auto
      have finite_M: "finite ?M" using finite_filter finite_imageI valid_finite by auto
      show "Mapping.lookup m' k = 
          (let group = Set.filter (\<lambda>x. agg_key b cs x = k) ?new_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
          in Some (size (int_mset_conv M), fold_mset (+) 0 (int_mset_conv M)))"
      proof(cases "agg_key b cs elem = k")
        case True
        then have k_def: "agg_key b cs elem = k" by auto
        then show ?thesis
        proof(cases "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) = {elem}")
          case True
          have in_M: "(meval_trm cs f elem, 1) \<in> ?old_M" using single_term_in_multiset[OF k_def True] by simp
          have mset_eq: "?M = ?old_M - {(meval_trm cs f elem, 1)}"
            using multiset_single_term_remove[OF k_def True] by simp
          then have not_in: "(meval_trm cs f elem, 1) \<notin> ?M" by auto
          have mset_insert: "?old_M = Set.insert (meval_trm cs f elem, 1) ?M" using in_M mset_eq by auto
          then have mset_conv_eq: "int_mset_conv ?old_M = add_mset i (int_mset_conv ?M)"
            using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ finite_M not_in] i_def
            by(simp add:int_mset_conv_def mset_conv_def unpack_int_def one_enat_def)
          have op1: "size (int_mset_conv ?M) = len - 1" using mset_conv_eq vals(1) by simp
          have op2: "fold_mset (+) 0 (int_mset_conv ?M) = sum - i"
            using mset_conv_eq Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ finite_old_M _] i_def vals(2)
            by(simp add:int_mset_conv_def mset_conv_def unpack_int_def one_enat_def)
          show ?thesis using k_in lookup_def * unfolding Let_def op1[unfolded group_multiset_def Let_def group_def] op2[unfolded group_multiset_def Let_def group_def] new_map_def k_def
            by auto 
        next
          case False
          then obtain n where n_def: "(meval_trm cs f elem, enat n) \<in> ?old_M" 
            using k_def in_set valid_finite_group_mset[OF finite_X, of k b cs f] finite_X
            by (auto simp: ecard_def)
          then have "n \<noteq> 0" by (metis enat_0_iff(1) finite_X valid_finite_group_mset valid_finite_mset_def)
          then obtain n' where "n' = n - 1" by auto
          then have n'_def: "(meval_trm cs f elem, enat (n' + 1)) \<in> ?old_M" using n_def \<open>n \<noteq> 0\<close> by force
          then have not_in: "(meval_trm cs f elem, enat n') \<notin> ?old_M" using unique_term_multiset[OF n'_def] by auto
          have "?M = Set.insert (meval_trm cs f elem, enat n') (?old_M - {(meval_trm cs f elem, enat (n' + 1))})"
            using multiset_multiple_term_remove[OF k_def False n'_def in_set finite_X] by simp 
          then have mset_conv_eq: "int_mset_conv ?old_M = add_mset i (int_mset_conv ?M)" 
            using mset_conv_insert_remove'[OF n'_def _ not_in finite_old_M, of unpack_int] i_def by(simp add:int_mset_conv_def unpack_int_def) 
          have op1: "size (int_mset_conv ?M) = len - 1" using mset_conv_eq vals(1) by simp
          have op2: "fold_mset (+) 0 (int_mset_conv ?M) = sum - i"
            using mset_conv_eq Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ finite_old_M not_in] i_def vals(2)
            by(simp add:int_mset_conv_def mset_conv_def unpack_int_def one_enat_def)
          show ?thesis using k_in lookup_def * unfolding Let_def op1[unfolded group_multiset_def Let_def group_def] op2[unfolded group_multiset_def Let_def group_def] new_map_def k_def
            by auto 
        qed
      next
        case False
        then have "Mapping.lookup m' k = Mapping.lookup m k" by (simp add: lookup_delete lookup_update' new_map_def)
        moreover have "group k b cs (X - {elem}) = group k b cs X" using False by auto
        ultimately show ?thesis using valid valid_before k_in b_def by(simp) (simp add: keys_is_none_rep)
      qed
    qed
    have "valid_maggaux ?args (SumAux m') (X - {elem})" 
      using b_def valid_finite valid_aggtype valid_type_restr valid_key_invariant valid_value_invariant by simp
    then show ?thesis using del_def by(simp only:Let_def) fastforce
  next
    case False
    then show ?thesis using del_def by auto
  qed
qed

lemma valid_delete_cnt_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (CntAux m) X" 
  and in_set: "elem \<in> X"
  shows "let (v', m') = delete_cnt \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> elem (v, m) in
      if v' then valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (CntAux m') (X - {elem})
      else True"
proof - 
  let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
  let ?new_data = "(X - {elem})"
  define b where "b = length tys"
  obtain v' m' where del_def: "(v', m') = delete_cnt ?args elem (v, m)" by (metis surj_pair)
  show ?thesis
  proof(cases v')
    case True
    then have valid: "v = True" using del_def by (auto split:if_splits)
    have finite_X: "finite X" using valid valid_before by auto
    then have valid_finite: "finite ?new_data" by auto
    have elem_in: "agg_key b cs elem \<in> Mapping.keys m" using in_set valid valid_before b_def by auto
    then obtain c where lookup_def: "Mapping.lookup m (agg_key b cs elem) = Some c" 
      using True del_def valid b_def by(auto simp: keys_is_none_rep split:option.splits)
    then have "c = length (flatten_multiset (group_multiset (agg_key b cs elem) b cs f X))" 
      using length_mset_eq[OF _ valid_finite_group_mset[OF finite_X, of "(agg_key b cs elem)" b cs f], of Some] 
      valid valid_before elem_in b_def by simp 
    then have c_def: "c = card(group (agg_key b cs elem) b cs X)" using finite_X length_flatten_multiset' by blast
    have new_map_def: "m' = (if c = 1 then Mapping.delete (agg_key b cs elem) m else Mapping.update (agg_key b cs elem) (c - 1) m)"
      using del_def valid lookup_def b_def by simp
    have valid_aggtype: "fst \<omega> = Formula.Agg_Cnt" using valid_before valid by auto
    have valid_type_restr: "type_restr ?args (X - {elem})" using valid_before valid by(auto simp:type_restr_def)
    have valid_key_invariant: "\<And>k. k \<in> (agg_key b cs) ` ?new_data \<longleftrightarrow> k \<in> Mapping.keys m'"
    proof (rule iffI)
      fix k
      assume assm: "k \<in> agg_key b cs ` (X - {elem})"
      show "k \<in> Mapping.keys m'" 
      proof(cases "agg_key b cs elem = k")
        case True
        from assm obtain e where e: "e \<in> X" "e \<noteq> elem" "agg_key b cs e = k" by auto
        have "c \<noteq> 1"
        proof
          assume "c = 1"
          then obtain z where "group (agg_key b cs elem) b cs X = {z}"
            unfolding c_def by (rule card_1_singletonE)
          moreover have "elem \<in> group (agg_key b cs elem) b cs X" "e \<in> group (agg_key b cs elem) b cs X"
            using in_set e True by auto
          ultimately show False using e(2) by (metis singletonD)
        qed
        then show ?thesis using True new_map_def by simp
      next
        case False
        then have "k \<in> (agg_key b cs) ` X" using assm valid_before by auto
        then have "k \<in> Mapping.keys m" using valid_before valid b_def by auto
        then show ?thesis using False new_map_def by auto
      qed
    next
      fix k
      assume assm: "k \<in> Mapping.keys m'" 
      then have in_map: "k \<in> Mapping.keys m" using new_map_def elem_in by(auto split:if_splits) 
      then have in_set: "k \<in> (agg_key b cs) ` X" using valid_before valid b_def by auto
      show "k \<in> (agg_key b cs) ` (X - {elem})"
      proof(cases "agg_key b cs elem = k")
        case True
        then have not_1: "c \<noteq> 1" using assm new_map_def by(auto split:option.splits)
        then have "card (group k b cs X) \<noteq> 1" using c_def True by(auto)
        moreover have "group k b cs X \<noteq> {}" using True assms by auto
        ultimately obtain k' where "k' \<in> group k b cs X" "k' \<noteq> elem" by (metis is_singletonI' is_singleton_altdef)
        then show ?thesis by auto
      next
        case False
        then show ?thesis using in_set by auto
      qed
    qed
  have valid_value_invariant: "\<And>k. k \<in> Mapping.keys m' \<longrightarrow> Mapping.lookup m' k = 
          (let group = Set.filter (\<lambda>x. agg_key b cs x = k) ?new_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
          in Some (size (mset_conv Some M)))"
  proof rule
      fix k
      assume k_in: "k \<in> Mapping.keys m'"
      let ?M = "group_multiset k b cs f ?new_data"
      let ?old_M = "group_multiset k b cs f X"
      obtain len where *: "Mapping.lookup m k = Some len" using k_in by (metis Optimized_Agg.lookup_delete elem_in insert_absorb is_none_simps(1) keys_is_none_rep keys_update new_map_def not_None_eq)
      then have k_in_old: "k \<in> Mapping.keys m" by (simp add: keys_is_none_rep)
      then have vals: "len = size (mset_conv Some ?old_M)"  using valid valid_before * k_in_old b_def by auto
      have finite_old_M: "finite ?old_M" using finite_filter finite_imageI valid_finite by auto
      have finite_M: "finite ?M" using finite_filter finite_imageI valid_finite by auto
      show "Mapping.lookup m' k = 
          (let group = Set.filter (\<lambda>x. agg_key b cs x = k) ?new_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
          in Some (size (mset_conv Some M)))"
      proof(cases "agg_key b cs elem = k")
        case True
        then have k_def: "agg_key b cs elem = k" by auto
        then show ?thesis
        proof(cases "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) = {elem}")
          case True
          have in_M: "(meval_trm cs f elem, 1) \<in> ?old_M" using single_term_in_multiset[OF k_def True] by simp
          have mset_eq: "?M = ?old_M - {(meval_trm cs f elem, 1)}"
            using multiset_single_term_remove[OF k_def True] by simp
          then have not_in: "(meval_trm cs f elem, 1) \<notin> ?M" by auto
          have mset_insert: "?old_M = Set.insert (meval_trm cs f elem, 1) ?M" using in_M mset_eq by auto
          then have mset_conv_eq: "mset_conv Some ?old_M = add_mset (meval_trm cs f elem) (mset_conv Some ?M)"
            using Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of Some] _ finite_M not_in] 
            by(simp add:mset_conv_def one_enat_def)
          have "size (mset_conv Some ?M) = len - 1" using mset_conv_eq vals(1) by simp
          then show ?thesis using new_map_def k_def k_in by(auto) (metis "*" local.lookup_def option.inject)
        next
          case False
          then obtain n where n_def: "(meval_trm cs f elem, enat n) \<in> ?old_M" 
            using k_def in_set valid_finite_group_mset[OF finite_X, of k b cs f] finite_X
            by (auto simp: ecard_def)
          then have "n \<noteq> 0" by (metis enat_0_iff(1) finite_X valid_finite_group_mset valid_finite_mset_def)
          then obtain n' where "n' = n - 1" by auto
          then have n'_def: "(meval_trm cs f elem, enat (n' + 1)) \<in> ?old_M" using n_def \<open>n \<noteq> 0\<close> by force
          then have not_in: "(meval_trm cs f elem, enat n') \<notin> ?old_M" using unique_term_multiset[OF n'_def] by auto
          have "?M = Set.insert (meval_trm cs f elem, enat n') (?old_M - {(meval_trm cs f elem, enat (n' + 1))})"
            using multiset_multiple_term_remove[OF k_def False n'_def in_set finite_X] by simp 
          then have mset_conv_eq: "mset_conv Some ?old_M = add_mset (meval_trm cs f elem) (mset_conv Some ?M)" 
            using mset_conv_insert_remove'[OF n'_def _ not_in finite_old_M, of Some] by simp
          have "size (mset_conv Some ?M) = len - 1" using mset_conv_eq vals(1) by simp
          then show ?thesis using new_map_def k_def k_in by(auto) (metis "*" local.lookup_def option.inject)
        qed
      next
        case False
        then have "Mapping.lookup m' k = Mapping.lookup m k" by (simp add: lookup_delete lookup_update' new_map_def)
        moreover have "group k b cs (X - {elem}) = group k b cs X" using False by auto
        ultimately show ?thesis using valid valid_before k_in b_def by(simp) (simp add: keys_is_none_rep)
      qed
    qed
    have "valid_maggaux ?args (CntAux m') (X - {elem})" 
      using valid_finite valid_aggtype valid_type_restr valid_key_invariant valid_value_invariant b_def by simp
    then show ?thesis using del_def by(simp only:Let_def) fastforce
  next
    case False
    then show ?thesis using del_def by auto
  qed
qed

lemma valid_list_aux_length_eq:
  assumes "valid_list_aux l (group_multiset k b cs f X) type"
  and "finite X"
  shows "get_length l = length (flatten_multiset (group_multiset k b cs f X))"
proof(cases l)
  case (LInt x1)
  then have "(\<And>t m. (t, m) \<in> group_multiset k b cs f X \<Longrightarrow> unpack_int t \<in> range Some)"
    using assms
    by(auto simp:unpack_int_def valid_list_aux_def valid_list_aux'_def type_restr_mset_def image_iff)
  then have "size (mset_conv unpack_int (group_multiset k b cs f X)) = length (flatten_multiset (group_multiset k b cs f X))"
    using length_mset_eq[OF _ valid_finite_group_mset[OF assms(2), of k b cs f], of unpack_int] by auto
  then show ?thesis using assms LInt
    by(auto simp:get_length_def treelist_size_eq int_mset_conv_def valid_list_aux_def valid_list_aux'_def) 
next
  case (LString x2)
  then have "(\<And>t m. (t, m) \<in> group_multiset k b cs f X \<Longrightarrow> unpack_string t \<in> range Some)"
    using assms by(auto simp:unpack_string_def valid_list_aux_def valid_list_aux'_def type_restr_mset_def image_iff)
  then have "size (mset_conv unpack_string (group_multiset k b cs f X)) = length (flatten_multiset (group_multiset k b cs f X))"
    using length_mset_eq[OF _ valid_finite_group_mset[OF assms(2), of k b cs f], of unpack_string] by auto
  then show ?thesis using assms LString
    by(auto simp:get_length_def treelist_size_eq str_mset_conv_def valid_list_aux_def valid_list_aux'_def) 
qed

lemma valid_delete_rank_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (RankAux (m, type)) X" 
  and in_set: "elem \<in> X"
  shows "let (v', m') = delete_rank \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> type elem (v, m) in
      if v' then valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> (RankAux (m', type)) (X - {elem})
      else True"
proof - 
  let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
  let ?new_data = "(X - {elem})"
  define b where "b = length tys"
  obtain v' m' where del_def: "(v', m') = delete_rank ?args type elem (v, m)" by (metis surj_pair)
  show ?thesis
  proof(cases v')
    case True
    then have valid_new: "v' = True" by auto
    then have valid: "v = True" using del_def by (auto split:if_splits)
    have finite_X: "finite X" using valid valid_before by auto
    then have valid_finite: "finite ?new_data" by auto
    have elem_in: "agg_key b cs elem \<in> Mapping.keys m" using in_set valid valid_before b_def by auto
    then obtain l where lookup_def: "Mapping.lookup m (agg_key b cs elem) = Some l" "valid_list_aux l (group_multiset (agg_key b cs elem) b cs f X) type"
      using True del_def valid valid_before b_def by(auto simp: keys_is_none_rep split:option.splits list_aux.splits list.splits event_data.splits)
    obtain i s where meval_def: "meval_trm cs f elem = EInt i \<or> meval_trm cs f elem = EString s" 
      using valid True del_def by(auto split:event_data.splits option.splits list_aux.splits list.splits)
    note * = subst[where P="\<lambda>x. x \<in> _", OF _ meval_in_set[OF in_set refl finite_X, where f=f]]
    have new_map_def: "m' = (case (l, meval_trm cs f elem) of
                            (LString t', EString term') \<Rightarrow> if term' \<in> set_treelist t' then let l' = remove_treelist term' t' in if l' = empty_treelist then Mapping.delete (agg_key b cs elem) m else Mapping.update (agg_key b cs elem) (LString l') m
                                                           else Mapping.empty |
                            (LInt t', EInt term') \<Rightarrow> if term' \<in> set_treelist t' then let l' = remove_treelist term' t' in if l' = empty_treelist then Mapping.delete (agg_key b cs elem) m else Mapping.update (agg_key b cs elem) (LInt l') m
                                                     else Mapping.empty)"
      using del_def valid meval_def True b_def lookup_def
        in_mset_in_list_int[OF * finite_X] in_mset_in_list_str[OF * finite_X]
      by (auto simp:lookup_def split:event_data.splits option.splits list_aux.splits list.splits type.splits)
    have restr: "l \<in> range LInt \<longleftrightarrow> meval_trm cs f elem \<in> range EInt" 
      using True del_def valid lookup_def b_def by(auto split: list_aux.splits event_data.splits list.splits)
    have elem_in_treelist: "case (l, meval_trm cs f elem) of
               (LString t', EString term') \<Rightarrow> term' \<in> set_treelist t' |
               (LInt t', EInt term') \<Rightarrow> term' \<in> set_treelist t'"
    proof(cases l)
      case (LInt x1)
      then obtain i where i_def: "meval_trm cs f elem = EInt i" using restr by auto
      have type_def: "type = IntT" using lookup_def(2) LInt by (cases type) (simp_all only: valid_list_aux_def list_aux.case type.case simp_thms)
      have k_id: "agg_key b cs elem = agg_key b cs elem" by auto
      have in_s: "meval_trm cs f elem \<in> set (flatten_multiset (group_multiset (agg_key b cs elem) b cs f X))" using meval_in_set[OF in_set k_id finite_X, where f=f] by auto
      then show ?thesis using in_mset_in_list_int[OF in_s[unfolded i_def] finite_X lookup_def(2)[unfolded LInt type_def]]  LInt i_def by auto
    next
      case (LString x2)
      then obtain s where s_def: "meval_trm cs f elem = EString s" using restr meval_def by auto
      have type_def: "type = StringT" using lookup_def(2) LString by (cases type) (simp_all only: valid_list_aux_def list_aux.case type.case simp_thms)
      have k_id: "agg_key b cs elem = agg_key b cs elem" by auto
      have in_s: "meval_trm cs f elem \<in> set (flatten_multiset (group_multiset (agg_key b cs elem) b cs f X))" using meval_in_set[OF in_set k_id finite_X, where f=f] by auto
      then show ?thesis using in_mset_in_list_str[OF in_s[unfolded s_def] finite_X lookup_def(2)[unfolded LString type_def]] LString s_def by auto
    qed
    have valid_aggtype: "fst \<omega> = Formula.Agg_Min \<or> fst \<omega> = Formula.Agg_Max \<or> fst \<omega> = Formula.Agg_Med" using valid_before valid by auto
    then have valid_type_restr: "(case type of IntT \<Rightarrow> (meval_trm cs f ` (X - {elem})) \<subseteq> range EInt | 
                                 StringT \<Rightarrow> (meval_trm cs f ` (X - {elem})) \<subseteq> range EString)" using valid_before valid 
      by(auto split:type.splits)
    have valid_key_invariant: "\<And>k. k \<in> (agg_key b cs) ` ?new_data \<longleftrightarrow> k \<in> Mapping.keys m'"
    proof (rule iffI)
      fix k
      assume assm: "k \<in> agg_key b cs ` (X - {elem})"
      show "k \<in> Mapping.keys m'" 
      proof(cases "agg_key b cs elem = k")
        case True
        then obtain k' where "k' \<in> X" "k' \<noteq> elem" "agg_key b cs k' = k" using assm by fastforce
        then have "card (Set.filter (\<lambda>x. agg_key b cs x = agg_key b cs elem) X) > 1" using True finite_X
          by (smt (verit, best) card_0_eq card_1_singleton_iff filter_insert finite_filter in_set
              insertCI insert_Diff singletonD)
        then have geq1: "get_length l > 1" using True length_flatten_multiset'[OF finite_X, of k b cs f] 
          valid_list_aux_length_eq[OF lookup_def(2) finite_X] by auto
        show ?thesis 
        proof(cases l)
          case (LInt x1)
          then have *: "length_treelist x1 > 1" using geq1 unfolding get_length_def by auto
          show ?thesis using treelist_del2[OF *] assm meval_def restr geq1 elem_in_treelist unfolding new_map_def True LInt 
            by(auto simp:get_length_def split:list_aux.splits list.splits if_splits) 
        next
          case (LString x2)
          then have *: "length_treelist x2 > 1" using geq1 unfolding get_length_def by auto
          then show ?thesis using treelist_del2[OF *] assm meval_def restr geq1 elem_in_treelist unfolding new_map_def True LString
            by(auto simp:get_length_def split:list_aux.splits list.splits if_splits) 
        qed
      next
        case False
        then have "k \<in> (agg_key b cs) ` X" using assm valid_before by auto
        then have "k \<in> Mapping.keys m" using valid_before valid b_def by auto
        then show ?thesis using restr new_map_def meval_def False elem_in_treelist by(auto split:list.splits list_aux.splits event_data.splits)
      qed
    next
      fix k
      assume assm: "k \<in> Mapping.keys m'" 
      then have in_map: "k \<in> Mapping.keys m" using new_map_def elem_in meval_def restr
        by(auto split:list_aux.splits list.splits if_splits) 
      then have in_set: "k \<in> (agg_key b cs) ` X" using valid_before valid b_def by auto
      show "k \<in> (agg_key b cs) ` (X - {elem})"
      proof(cases "agg_key b cs elem = k")
        case True
        have not_1: "get_length l \<noteq> 1"
        proof
          assume len: "get_length l = 1"
          have "m' = Mapping.delete (agg_key b cs elem) m"
          proof (cases l)
            case (LInt t)
            then obtain j where j: "meval_trm cs f elem = EInt j" using restr by auto
            then have "j \<in> set_treelist t" "length_treelist t = 1"
              using elem_in_treelist len LInt by (simp_all add: get_length_def)
            then have "remove_treelist j t = empty_treelist" by (rule treelist_del1[rotated])
            then show ?thesis using new_map_def LInt j \<open>j \<in> set_treelist t\<close> by simp
          next
            case (LString t)
            then obtain j where j: "meval_trm cs f elem = EString j" using restr meval_def by auto
            then have "j \<in> set_treelist t" "length_treelist t = 1"
              using elem_in_treelist len LString by (simp_all add: get_length_def)
            then have "remove_treelist j t = empty_treelist" by (rule treelist_del1[rotated])
            then show ?thesis using new_map_def LString j \<open>j \<in> set_treelist t\<close> by simp
          qed
          then show False using assm True by simp
        qed
        then have "card (group k b cs X) \<noteq> 1" using True valid_list_aux_length_eq[OF lookup_def(2) finite_X] length_flatten_multiset'[OF finite_X, of k b cs f] by(auto)
        moreover have "group k b cs X \<noteq> {}" using True assms by auto
        ultimately obtain k' where "k' \<in> group k b cs X" "k' \<noteq> elem" by (metis is_singletonI' is_singleton_altdef)
        then show ?thesis by auto
      next
        case False
        then show ?thesis using in_set by auto
      qed
    qed
  have valid_value_invariant: "\<And>k. k \<in> Mapping.keys m' \<longrightarrow> (case Mapping.lookup m' k of
      Some t \<Rightarrow> (let group = Set.filter (\<lambda>x. agg_key b cs x = k) ?new_data;
                 M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
                 in valid_list_aux t M type) |
      None \<Rightarrow> False)"
  proof rule
      fix k
      assume k_in: "k \<in> Mapping.keys m'"
      then obtain laux' where lookup_new: "Mapping.lookup m' k = Some laux'" using k_in by (metis domD keys_dom_lookup)
      have k_in_old: "k \<in> Mapping.keys m" using k_in new_map_def meval_def elem_in restr by(auto split:list_aux.splits list.splits if_splits)
      then obtain laux where lookup_old: "Mapping.lookup m k = Some laux" using k_in by (metis domD keys_dom_lookup)
      let ?M = "group_multiset k b cs f ?new_data"
      let ?old_M = "group_multiset k b cs f X"
      have enat_one: "the_enat 1 = 1" by (metis enat_1 the_enat.simps)
      have vals: "valid_list_aux laux ?old_M type"  using valid valid_before k_in_old lookup_old b_def by auto
      have finite_old_M: "finite ?old_M" using finite_filter finite_imageI valid_finite by auto
      have finite_M: "finite ?M" using finite_filter finite_imageI valid_finite by auto
      show "(case Mapping.lookup m' k of
      Some t \<Rightarrow> (let group = Set.filter (\<lambda>x. agg_key b cs x = k) ?new_data;
                 M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
                 in valid_list_aux t M type) |
      None \<Rightarrow> False)"
      proof(cases "agg_key b cs elem = k")
        case True
        then have k_def: "agg_key b cs elem = k" by auto
        have leq: "l = laux" using lookup_def(1) lookup_old k_def by auto
        then have "get_length l \<noteq> 1" using lookup_new[unfolded new_map_def] meval_def restr treelist_del1[of _ i] treelist_del1[of _ s]
          by(auto simp:get_length_def lookup_delete k_def split:list_aux.splits list.splits if_splits) 
        moreover have "get_length l \<noteq> 0"
        proof (cases l)
          case (LInt t)
          then obtain j where "meval_trm cs f elem = EInt j" using restr by auto
          then have "j \<in> set_treelist t" using elem_in_treelist LInt by simp
          then show ?thesis using LInt treelist_empty[of t] by (auto simp: get_length_def)
        next
          case (LString t)
          then obtain j where "meval_trm cs f elem = EString j" using restr meval_def by auto
          then have "j \<in> set_treelist t" using elem_in_treelist LString by simp
          then show ?thesis using LString treelist_empty[of t] by (auto simp: get_length_def)
        qed
        ultimately have geq1: "get_length l > 1" by auto
        have list_elem_restr: "\<forall>l. Mapping.lookup m k = Some (LInt l) \<longrightarrow> meval_trm cs f elem \<in> range EInt"
                            "\<forall>l. Mapping.lookup m k = Some (LString l) \<longrightarrow> meval_trm cs f elem \<in> range EString"
          using True del_def valid valid_new b_def by(auto split:event_data.splits option.splits list.splits)
        have laux_rel: "laux' = (case (l, meval_trm cs f elem) of
                            (LString t', EString term') \<Rightarrow> LString (remove_treelist term' t') |
                            (LInt t', EInt term') \<Rightarrow> LInt (remove_treelist term' t'))"
          using lookup_def(1) True restr meval_def lookup_new[unfolded new_map_def]  treelist_del2 geq1
          by(auto simp:get_length_def split:list_aux.splits event_data.splits list.splits if_splits) 
        have "valid_list_aux laux' ?M type"
        proof(cases "Set.filter (\<lambda>x. meval_trm cs f x = meval_trm cs f elem) (group k b cs X) = {elem}")
          case True
          have in_M: "(meval_trm cs f elem, 1) \<in> ?old_M" using single_term_in_multiset[OF k_def True] by simp
          have mset_eq: "?M = ?old_M - {(meval_trm cs f elem, 1)}"
            using multiset_single_term_remove[OF k_def True] by simp
          then have not_in: "(meval_trm cs f elem, 1) \<notin> ?M" by auto
          have mset_insert: "?old_M = Set.insert (meval_trm cs f elem, 1) ?M" using in_M mset_eq by auto
          show ?thesis 
          proof(cases l)
            case (LInt li)
            then obtain i where i_def: "meval_trm cs f elem = EInt i" using restr by auto
            then have *: "i \<in> set_treelist li" using elem_in_treelist LInt by auto
            have mset_conv_rel: "int_mset_conv ?M = int_mset_conv ?old_M - {#i#}" using mset_insert Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ finite_M not_in] i_def enat_one
              by(auto simp:int_mset_conv_def mset_conv_def unpack_int_def) 
            show ?thesis using mset_remove_treelist[of i li] vals
              unfolding valid_list_aux_def valid_list_aux'_def leq[symmetric] LInt type_restr_mset_def mset_conv_rel i_def laux_rel
              by auto fastforce
          next
            case (LString ls)
            then obtain i where i_def: "meval_trm cs f elem = EString i" using restr meval_def by auto
            then have *: "i \<in> set_treelist ls" using elem_in_treelist LString by auto
            have mset_conv_rel: "str_mset_conv ?M = str_mset_conv ?old_M - {#i#}" using mset_insert Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_string] _ finite_M not_in] i_def enat_one
              by(auto simp:str_mset_conv_def mset_conv_def unpack_string_def) 
            show ?thesis using mset_remove_treelist[of i ls] vals
              unfolding valid_list_aux_def valid_list_aux'_def leq[symmetric] LString type_restr_mset_def mset_conv_rel i_def laux_rel
              by auto fastforce
          qed
        next
          case False
          then obtain n where n_def: "(meval_trm cs f elem, enat n) \<in> ?old_M" 
            using k_def in_set valid_finite_group_mset[OF finite_X, of k b cs f] finite_X
            by (auto simp: ecard_def image_iff)
          then have "n \<noteq> 0" by (metis enat_0_iff(1) finite_X valid_finite_group_mset valid_finite_mset_def)
          then obtain n' where "n' = n - 1" by auto
          then have n'_def: "(meval_trm cs f elem, enat (n' + 1)) \<in> ?old_M" using n_def \<open>n \<noteq> 0\<close> by force
          then have not_in: "(meval_trm cs f elem, enat n') \<notin> ?old_M" using unique_term_multiset[OF n'_def] by auto
          have mset_rel: "?M = Set.insert (meval_trm cs f elem, enat n') (?old_M - {(meval_trm cs f elem, enat (n' + 1))})"
            using multiset_multiple_term_remove[OF k_def False n'_def in_set finite_X] by simp 
          show ?thesis 
          proof(cases l)
            case (LInt li)
            then obtain i where i_def: "meval_trm cs f elem = EInt i" using restr by auto
            then have *: "i \<in> set_treelist li" using elem_in_treelist LInt by auto
            have mset_conv_rel: "int_mset_conv ?M = int_mset_conv ?old_M - {#i#}" using mset_conv_insert_remove'[OF n'_def _ not_in finite_old_M, of unpack_int] mset_rel i_def
              by(simp add:int_mset_conv_def unpack_int_def) (metis (no_types, lifting) add_mset_remove_trivial)
            show ?thesis using mset_remove_treelist[of i li] vals
              unfolding valid_list_aux_def valid_list_aux'_def leq[symmetric] LInt type_restr_mset_def mset_conv_rel i_def laux_rel
              by fastforce
          next
            case (LString ls)
            then obtain i where i_def: "meval_trm cs f elem = EString i" using restr meval_def by auto
            then have *: "i \<in> set_treelist ls" using elem_in_treelist LString by auto
            have mset_conv_rel: "str_mset_conv ?M = str_mset_conv ?old_M - {#i#}" using mset_conv_insert_remove'[OF n'_def _ not_in finite_old_M, of unpack_string] mset_rel i_def
              by(simp add:str_mset_conv_def unpack_string_def) (metis (no_types, lifting) add_mset_remove_trivial)
            show ?thesis using mset_remove_treelist[of i ls] vals
              unfolding valid_list_aux_def valid_list_aux'_def leq[symmetric] LString type_restr_mset_def mset_conv_rel i_def laux_rel
              by fastforce
          qed
        qed
        then show ?thesis using lookup_new by auto
      next
        case False
        then have "Mapping.lookup m' k = Mapping.lookup m k" using restr meval_def elem_in_treelist
          by(auto simp: lookup_delete lookup_update' new_map_def split:list_aux.splits list.splits event_data.splits)
        moreover have "group k b cs (X - {elem}) = group k b cs X" using False by auto
        ultimately show ?thesis using valid valid_before k_in b_def by(auto simp add: keys_is_none_rep split:option.splits)
      qed
    qed
    have "valid_maggaux ?args (RankAux (m', type)) (X - {elem})" 
      using b_def valid_finite valid_aggtype valid_type_restr valid_key_invariant valid_value_invariant by (simp del: Set.filter_eq) meson
    then show ?thesis using del_def by(simp only:Let_def) fastforce
  next
    case False
    then show ?thesis unfolding del_def[symmetric] by auto
  qed
qed


lemma valid_delete_maggaux_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> aux X"
  and subset: "Y \<subseteq> X"
shows "let (v', aux') = delete_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> Y aux in
  if v' then valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> aux' (X - Y)
  else True"
proof -
  have finite_Y: "finite Y" using valid_before finite_subset subset by auto
  show ?thesis using valid_before
  proof(induction aux)
    case (CntAux m)
    show ?case using finite_Y subset CntAux
    proof(induction Y)
      case empty
      then show ?case  by auto
    next
      case (insert x F)
      let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
      interpret comp_fun_commute "delete_cnt ?args"
        using delete_cnt_comm by unfold_locales auto
      obtain v' m' where intermediate_map_def: "(v', CntAux m') = delete_maggaux ?args F (CntAux m)" 
        by (cases "Finite_Set.fold (delete_cnt ?args) (True, m) F") auto
      then have fold_def: "Finite_Set.fold (delete_cnt ?args) (True, m) F = (v', m')" 
        by(auto split:prod.splits)
      obtain v_f m_f where final_map_def: "(v_f, m_f) = delete_cnt ?args x (v', m')" by auto metis
      show ?case
      proof (cases v_f)
        case True 
        have subs: "F \<subseteq> X" using insert(4) by force
        have x_in: "x \<in> X - F" using insert by auto
        have int_true: "v' = True" using True final_map_def by auto (metis Pair_inject)
        then have valid_inter: "valid_maggaux ?args (CntAux m') (X - F)" 
          using insert(3)[OF subs CntAux] fold_def by(simp add:intermediate_map_def split:prod.splits) 
        have "valid_maggaux ?args (CntAux m_f) (X - F - {x})"
          using valid_delete_cnt_unfolded[OF valid_inter x_in, of v'] final_map_def True int_true by simp
        then have "valid_maggaux ?args (CntAux m_f) (X - Set.insert x F)" by (metis Diff_insert)
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def True
          by(simp cong:option.case_cong del:delete_cnt.simps valid_maggaux.simps split:prod.splits) force
      next
        case False
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def 
          by(simp del:insert_cnt.simps valid_maggaux.simps split:prod.splits) force
      qed
    qed
  next
    case (SumAux m)
    show ?case using finite_Y subset SumAux
    proof(induction Y)
      case empty
      then show ?case by auto 
    next
      case (insert x F)
      let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
      interpret comp_fun_commute "delete_sum ?args"
        using delete_sum_comm by unfold_locales auto
      obtain v' m' where intermediate_map_def: "(v', SumAux m') = delete_maggaux ?args F (SumAux m)" 
        by (cases "Finite_Set.fold (delete_sum ?args) (True, m) F") auto
      then have fold_def: "Finite_Set.fold (delete_sum ?args) (True, m) F = (v', m')" 
        by(auto split:prod.splits)
      obtain v_f m_f where final_map_def: "(v_f, m_f) = delete_sum ?args x (v', m')" using prod.collapse by blast
      show ?case
      proof (cases v_f)
        case True 
        have subs: "F \<subseteq> X" using insert(4) by force
        have x_in: "x \<in> X - F" using insert by auto
        have int_true: "v' = True" using True final_map_def by auto (metis Pair_inject)
        then have valid_inter: "valid_maggaux ?args (SumAux m') (X - F)" 
          using insert(3)[OF subs SumAux] fold_def by(simp add:intermediate_map_def split:prod.splits) 
        have "valid_maggaux ?args (SumAux m_f) (X - F - {x})"
          using valid_delete_sum_unfolded[OF valid_inter x_in, of v'] final_map_def True int_true by (simp split:prod.splits)
        then have "valid_maggaux ?args (SumAux m_f) (X - Set.insert x F)" by (metis Diff_insert)
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def True
          by(simp cong:option.case_cong del:delete_cnt.simps valid_maggaux.simps split:prod.splits) force
      next
        case False
        then show ?thesis using fold_insert[OF insert(1-2)] final_map_def fold_def 
          by(simp del:insert_cnt.simps valid_maggaux.simps split:prod.splits) force
      qed
    qed
  next
    case (RankAux aux)
    then obtain m type where [simp]: "aux = (m, type)" by (meson surj_pair)
    let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
    show ?case using finite_Y subset RankAux
    proof(induction Y)
      case empty
      then show ?case by auto 
    next
      case (insert x F)
      interpret comp_fun_commute "delete_rank ?args type"
        using delete_rank_comm by unfold_locales auto
      obtain v' m' where intermediate_map_def: "(v', m') = Finite_Set.fold (delete_rank ?args type) (True, m) F" 
        using prod.collapse by blast
      then have fold_def: "Finite_Set.fold (delete_rank ?args type) (True, m) F = (v', m')" 
        by(auto split:prod.splits)
      obtain v_f m_f where final_map_def: "(v_f, m_f) = delete_rank ?args type x (v', m')" using prod.collapse by blast
      have del: "delete_maggaux ?args (Set.insert x F) (RankAux aux) = (v_f, RankAux (m_f, type))"
        by (simp add: fold_insert[OF insert(1-2)] fold_def final_map_def[symmetric] del: delete_rank.simps)
      show ?case
      proof (cases v_f)
        case True 
        have subs: "F \<subseteq> X" using insert(4) by force
        have x_in: "x \<in> X - F" using insert by auto
        have int_true: "v' = True" using True final_map_def by auto (metis Pair_inject)
        then have valid_inter: "valid_maggaux ?args (RankAux (m', type)) (X - F)" 
          using insert(3)[OF subs RankAux] fold_def by(simp add:intermediate_map_def split:prod.splits) 
        have "valid_maggaux ?args (RankAux (m_f, type)) (X - F - {x})"
          using valid_delete_rank_unfolded[OF valid_inter x_in, of v'] final_map_def True int_true by (simp split:prod.splits)
        then have "valid_maggaux ?args (RankAux (m_f, type)) (X - Set.insert x F)" by (metis Diff_insert)
        then show ?thesis using del True by simp
      next
        case False
        then show ?thesis using del by simp
      qed
    qed
  qed
qed

lemma valid_delete_maggaux: "valid_maggaux args aux X \<Longrightarrow>
    Y \<subseteq> X \<Longrightarrow>
    let (v', aux') = delete_maggaux args Y aux in if v' then valid_maggaux args aux' (X - Y) else True"
  using valid_delete_maggaux_unfolded by (cases args) blast

lemma plus'_aux: "(plus' x \<circ> plus' y) z = (plus' y \<circ> plus' x) z"
  by(cases x, cases y, cases z) auto

lemma comp_fun_commute_plus': "comp_fun_commute plus'"
  using plus'_aux by unfold_locales auto

lemma comm_plus': "plus' x y = plus' y x"
  by(cases x, cases y) auto

lemma foldl_eint_equival: 
  assumes "set X \<subseteq> range EInt"
  and "y0 \<in> range EInt"
  shows "foldl (+) y0 X = foldl (plus') y0 X"
  using assms
proof(induction X arbitrary: y0)
case Nil
  then show ?case by auto
next
  case (Cons a X)
  then show ?case using Cons by auto
qed

lemma foldl_int_eq':
  assumes "\<forall>t m. ((t, m) \<in> s \<longrightarrow> t \<in> range EInt)"
  and "valid_finite_mset s"
  shows "EInt (fold_mset (+) 0 (int_mset_conv s)) = foldl (+) (EInt 0) (flatten_multiset s)"
proof -
  have int_comm: "comp_fun_commute ((+)::integer \<Rightarrow> integer \<Rightarrow> integer)"
    by unfold_locales auto
  have finite: "finite s" using assms(2) by (simp add:valid_finite_mset_def)
  have int: "set (flatten_multiset s) \<subseteq> range EInt" using flatten_multiset_range[of s EInt] assms(1) 
      finite by auto
  have aux: "comp_fun_commute_on UNIV (\<lambda>(t, m). plus' t ^^ the_enat m)" using cmp_comm[OF comp_fun_commute_plus']
    by unfold_locales auto
  show ?thesis using finite assms(1-2) int
  proof(induction s)
    case empty
    then show ?case using finite foldl_eint_equival[OF empty(3)]
      foldl_flatten_multiset[OF _ comp_fun_commute_plus' comm_plus'] 
      by(simp add:int_mset_conv_def mset_conv_def)
  next
    case (insert x F)
    have *: "valid_finite_mset F" by (metis insert.hyps(1) insert.prems(2) insert_iff valid_finite_mset_def)
    have **: "\<forall>t m. (t, m) \<in> F \<longrightarrow> t \<in> range EInt" using insert(4) by auto
    then have ***: "set (flatten_multiset F) \<subseteq> range EInt" using flatten_multiset_range[OF _ insert(1), of EInt] by auto 
    obtain i n where x_def: "x = (EInt i, enat n)" "n > 0" using insert(4-5) by (metis enat_ord_simps(4) insertI1 less_infinityE rangeE surj_pair valid_finite_mset_def zero_enat_def zero_less_iff_neq_zero)
    have "EInt (fold_mset (+) 0 (replicate_mset n i + int_mset_conv F)) = (plus' (EInt i) ^^ n) (EInt (fold_mset (+) 0 (int_mset_conv F)))"
    proof(induction n)
      case 0
      then show ?case by auto
    next
      case (Suc n)
      have *: "EInt (i + fold_mset (+) 0 (replicate_mset n i + int_mset_conv F)) = plus' (EInt i) (EInt (fold_mset (+) 0 (replicate_mset n i + int_mset_conv F)))"
        by auto
      then show ?case using comp_fun_commute.fold_mset_add_mset[OF int_comm] Suc by auto
    qed
    then show ?case using foldl_eint_equival[OF insert(6)] insert(1) x_def
      foldl_eint_equival[OF ***]
      foldl_flatten_multiset[OF _ comp_fun_commute_plus' comm_plus'] 
      Finite_Set.comp_fun_commute_on.fold_insert[OF aux _ insert(1-2)] insert.IH[OF ** * ***, symmetric]
      Finite_Set.comp_fun_commute_on.fold_insert[OF mset_conv_comm[of unpack_int] _ insert(1-2)]
      by(simp add:int_mset_conv_def mset_conv_def unpack_int_def)
  qed
qed

lemma foldl_int_eq:
  assumes "\<forall>t m. ((t, m) \<in> s \<longrightarrow> t \<in> range EInt)"
  and "valid_finite_mset s"
  and "flatten_multiset s = x # xs"
  shows "EInt (fold_mset (+) 0 (int_mset_conv s)) = foldl (+) x xs"
proof -
  have "EInt (fold_mset (+) 0 (int_mset_conv s)) = foldl (+) (EInt 0) (flatten_multiset s)" 
    using foldl_int_eq'[OF assms(1-2)] by auto
  moreover obtain i where "x = EInt i" using flatten_multiset_range[of s EInt] assms
    by(simp add:valid_finite_mset_def) (meson rangeE)
  ultimately show ?thesis using assms(3) by simp
qed

lemma valid_get_edata_list:
  assumes "valid_list_aux l s type"
  and "valid_finite_mset s"
  and "n \<ge> 0" and "n < get_length l"
  shows "get_edata_list l n = flatten_multiset s ! n"
proof -
  obtain c where c_def: "ID ccompare = Some (c :: event_data comparator)" 
    by (simp add: ID_def ccompare_event_data_def split:if_splits option.splits)
  have finite: "finite s" using assms(2) valid_finite_mset_def by auto
  then show ?thesis 
  proof(cases l)
    case (LInt x1)
    then have valid: "valid_list_aux' x1 (mset_conv unpack_int s)" 
      using assms(1) by(auto simp:int_mset_conv_def valid_list_aux_def)
    have surj: "\<forall>t m. (t, m) \<in> s \<longrightarrow> (\<exists>k. unpack_int t = Some k)"
      using assms(1) LInt by(auto simp:int_mset_conv_def valid_list_aux_def type_restr_mset_def unpack_int_def)
    have ord_preserve: " \<forall>t1 m1 t2 m2. (t1, m1) \<in> s \<and> (t2, m2) \<in> s \<longrightarrow> c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_int t1)) (the (unpack_int t2))"
      using assms(1) LInt int_cmp_eq[OF c_def] by(auto simp:valid_list_aux_def type_restr_mset_def) meson
    note sort_eq = sort_flatten_mset_eq[OF c_def valid assms(2) surj ord_preserve]
    have "n < length (flatten_multiset s)" 
      using assms(4)[unfolded get_length_def LInt] sort_eq treelist_length_eq[of x1] by simp
    moreover have "flatten_multiset s ! n \<in> range EInt" 
      using flatten_multiset_range[OF _ finite, of EInt] nth_mem[OF calculation(1)] assms(1) LInt
      by(auto simp:valid_list_aux_def valid_list_aux'_def type_restr_mset_def)
    ultimately show ?thesis using sort_eq unfolding LInt get_edata_list.simps by(transfer) (auto simp: unpack_int_def)
  next
    case (LString x2)
    then have valid: "valid_list_aux' x2 (mset_conv unpack_string s)" 
      using assms(1) by(auto simp:str_mset_conv_def valid_list_aux_def)
    have surj: "\<forall>t m. (t, m) \<in> s \<longrightarrow> (\<exists>k. unpack_string t = Some k)"
      using assms(1) LString by(auto simp:str_mset_conv_def valid_list_aux_def type_restr_mset_def unpack_string_def)
    have ord_preserve: " \<forall>t1 m1 t2 m2. (t1, m1) \<in> s \<and> (t2, m2) \<in> s \<longrightarrow> c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_string t1)) (the (unpack_string t2))"
      using assms(1) LString str_cmp_eq[OF c_def] by(auto simp:valid_list_aux_def type_restr_mset_def) meson
    note sort_eq = sort_flatten_mset_eq[OF c_def valid assms(2) surj ord_preserve]
    have "n < length (flatten_multiset s)" 
      using assms(4)[unfolded get_length_def LString] sort_eq treelist_length_eq[of x2] by simp
    moreover have "flatten_multiset s ! n \<in> range EString" 
      using flatten_multiset_range[OF _ finite, of EString] nth_mem[OF calculation(1)] assms(1) LString
      by(auto simp:valid_list_aux_def valid_list_aux'_def type_restr_mset_def)
    ultimately show ?thesis using sort_eq unfolding LString get_edata_list.simps by(transfer) (auto simp: unpack_string_def) 
  qed
qed

lemma unpack_foldl_min_eq_int:
  assumes "x \<in> range EInt"
  and "set xs \<subseteq> range EInt"
  shows "EInt (foldl min (the (unpack_int x)) (map (\<lambda>a. the (unpack_int a)) xs)) = foldl min x xs"
  using assms
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by (auto simp: unpack_int_def)
next
  case (Cons a xs)
  from Cons.prems obtain i j where x: "x = EInt i" and a: "a = EInt j" by auto
  have min_eq: "min (EInt i) (EInt j) = EInt (min i j)" by (simp add: min_def)
  have "EInt (foldl min (min i j) (map (\<lambda>a. the (unpack_int a)) xs)) = foldl min (EInt (min i j)) xs"
    using Cons.IH[of "EInt (min i j)"] Cons.prems by (simp add: unpack_int_def)
  then show ?case by (simp add: x a min_eq unpack_int_def)
qed

lemma unpack_foldl_min_eq_str:
  assumes "x \<in> range EString"
  and "set xs \<subseteq> range EString"
  shows "EString (foldl min (the (unpack_string x)) (map (\<lambda>a. the (unpack_string a)) xs)) = foldl min x xs"
  using assms
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by (auto simp: unpack_string_def)
next
  case (Cons a xs)
  from Cons.prems obtain i j where x: "x = EString i" and a: "a = EString j" by auto
  have min_eq: "min (EString i) (EString j) = EString (min i j)" by (simp add: min_def)
  have "EString (foldl min (min i j) (map (\<lambda>a. the (unpack_string a)) xs)) = foldl min (EString (min i j)) xs"
    using Cons.IH[of "EString (min i j)"] Cons.prems by (simp add: unpack_string_def)
  then show ?case by (simp add: x a min_eq unpack_string_def)
qed

lemma unpack_foldl_max_eq_int:
  assumes "x \<in> range EInt"
  and "set xs \<subseteq> range EInt"
  shows "EInt (foldl max (the (unpack_int x)) (map (\<lambda>a. the (unpack_int a)) xs)) = foldl max x xs"
  using assms
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by (auto simp: unpack_int_def)
next
  case (Cons a xs)
  from Cons.prems obtain i j where x: "x = EInt i" and a: "a = EInt j" by auto
  have max_eq: "max (EInt i) (EInt j) = EInt (max i j)" by (simp add: max_def)
  have "EInt (foldl max (max i j) (map (\<lambda>a. the (unpack_int a)) xs)) = foldl max (EInt (max i j)) xs"
    using Cons.IH[of "EInt (max i j)"] Cons.prems by (simp add: unpack_int_def)
  then show ?case by (simp add: x a max_eq unpack_int_def)
qed

lemma unpack_foldl_max_eq_str:
  assumes "x \<in> range EString"
  and "set xs \<subseteq> range EString"
  shows "EString (foldl max (the (unpack_string x)) (map (\<lambda>a. the (unpack_string a)) xs)) = foldl max x xs"
  using assms
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by (auto simp: unpack_string_def)
next
  case (Cons a xs)
  from Cons.prems obtain i j where x: "x = EString i" and a: "a = EString j" by auto
  have max_eq: "max (EString i) (EString j) = EString (max i j)" by (simp add: max_def)
  have "EString (foldl max (max i j) (map (\<lambda>a. the (unpack_string a)) xs)) = foldl max (EString (max i j)) xs"
    using Cons.IH[of "EString (max i j)"] Cons.prems by (simp add: unpack_string_def)
  then show ?case by (simp add: x a max_eq unpack_string_def)
qed

lemma valid_list_aux_min:
  assumes "valid_list_aux l (group_multiset k b cs f X) type"
  and "finite X"
  and "flatten_multiset (group_multiset k b cs f X) = x # xs"
shows "get_edata_list l 0 = foldl min x xs"
proof -
  let ?s = "group_multiset k b cs f X"
  obtain c where c_def: "ID ccompare = Some (c :: event_data comparator)" 
    by (simp add: ID_def ccompare_event_data_def split:if_splits option.splits)
  show ?thesis
proof(cases l)
  case (LInt x1)
  then have valid: "valid_list_aux' x1 (mset_conv unpack_int ?s)" 
    using assms(1) by(auto simp:int_mset_conv_def valid_list_aux_def)
  have surj: "\<forall>t m. (t, m) \<in> ?s \<longrightarrow> (\<exists>k. unpack_int t = Some k)"
    using assms(1) LInt by(auto simp:int_mset_conv_def valid_list_aux_def type_restr_mset_def unpack_int_def split:event_data.splits)
  have ord_preserve: " \<forall>t1 m1 t2 m2. (t1, m1) \<in> ?s \<and> (t2, m2) \<in> ?s \<longrightarrow> c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_int t1)) (the (unpack_int t2))"
    using assms(1) LInt int_cmp_eq[OF c_def] by(auto simp:valid_list_aux_def type_restr_mset_def image_iff)
  note sort_eq = sort_flatten_mset_eq[OF c_def valid valid_finite_group_mset[OF assms(2)] surj ord_preserve]
  have "set (x # xs) \<subseteq> range EInt"
  proof -
    have "type_restr_mset EInt ?s" using assms(1) LInt by (simp add: valid_list_aux_def)
    moreover have "finite ?s" using assms(2) by simp
    ultimately have "set (flatten_multiset ?s) \<subseteq> range EInt"
      by (intro flatten_multiset_range) (auto simp only: type_restr_mset_def)
    then show ?thesis unfolding assms(3) .
  qed
  then have type_restr: "x \<in> range EInt" "set xs \<subseteq> range EInt" by auto
  have "sorted_treelist (sort_treelist x1)" by(transfer) (metis sorted_sort)
  moreover obtain x' xs' where unpack_def: "map (\<lambda>a. the (unpack_int a)) (x # xs) = x' # xs'" "x' = the (unpack_int x)" "xs' = map (\<lambda>a. the (unpack_int a)) xs" by force
 have "sorted (map (\<lambda>a. the (unpack_int a)) (x # xs))" unfolding sort_eq[unfolded assms(3), symmetric] by (transfer; simp)
  then have *: "sorted (x' # xs')" unfolding unpack_def(1)[symmetric] unpack_def(2-3) by auto
  show ?thesis unfolding LInt get_edata_list.simps 
    using sort_eq[unfolded assms(3) unpack_def(1)] sorted_foldl_min[OF *, symmetric]  unpack_foldl_min_eq_int[OF type_restr] unfolding unpack_def(2-3) by transfer auto
next
  case (LString x2)
  then have valid: "valid_list_aux' x2 (mset_conv unpack_string ?s)" 
    using assms(1) by(auto simp:str_mset_conv_def valid_list_aux_def)
  have surj: "\<forall>t m. (t, m) \<in> ?s \<longrightarrow> (\<exists>k. unpack_string t = Some k)"
    using assms(1) LString by(auto simp:str_mset_conv_def valid_list_aux_def type_restr_mset_def unpack_string_def split:event_data.splits)
  have ord_preserve: " \<forall>t1 m1 t2 m2. (t1, m1) \<in> ?s \<and> (t2, m2) \<in> ?s \<longrightarrow> c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_string t1)) (the (unpack_string t2))"
    using assms(1) LString str_cmp_eq[OF c_def] by(auto simp:valid_list_aux_def type_restr_mset_def image_iff)
  note sort_eq = sort_flatten_mset_eq[OF c_def valid valid_finite_group_mset[OF assms(2)] surj ord_preserve]
  have "set (x # xs) \<subseteq> range EString"
  proof -
    have "type_restr_mset EString ?s" using assms(1) LString by (simp add: valid_list_aux_def)
    moreover have "finite ?s" using assms(2) by simp
    ultimately have "set (flatten_multiset ?s) \<subseteq> range EString"
      by (intro flatten_multiset_range) (auto simp only: type_restr_mset_def)
    then show ?thesis unfolding assms(3) .
  qed
  then have type_restr: "x \<in> range EString" "set xs \<subseteq> range EString" by auto
  have "sorted_treelist (sort_treelist x2)" by(transfer) (metis sorted_sort)
  moreover obtain x' xs' where unpack_def: "map (\<lambda>a. the (unpack_string a)) (x # xs) = x' # xs'" "x' = the (unpack_string x)" "xs' = map (\<lambda>a. the (unpack_string a)) xs" by force
  have "sorted (map (\<lambda>a. the (unpack_string a)) (x # xs))" unfolding sort_eq[unfolded assms(3), symmetric] by (transfer; simp)
  then have *: "sorted (x' # xs')" unfolding unpack_def(1)[symmetric] unpack_def(2-3) by auto
  show ?thesis unfolding LString get_edata_list.simps 
    using sort_eq[unfolded assms(3) unpack_def(1)] sorted_foldl_min[OF *, symmetric]  unpack_foldl_min_eq_str[OF type_restr] unfolding unpack_def(2-3) by transfer auto
qed
qed

lemma valid_list_aux_max:
  assumes "valid_list_aux l (group_multiset k b cs f X) type"
  and "finite X"
  and "flatten_multiset (group_multiset k b cs f X) = x # xs"
shows "get_edata_list l (size (x # xs) - 1) = foldl max x xs"
proof -
  let ?s = "group_multiset k b cs f X"
  obtain c where c_def: "ID ccompare = Some (c :: event_data comparator)" 
    by (simp add: ID_def ccompare_event_data_def split:if_splits option.splits)
  show ?thesis
proof(cases l)
  case (LInt x1)
  then have valid: "valid_list_aux' x1 (mset_conv unpack_int ?s)" 
    using assms(1) by(auto simp:int_mset_conv_def valid_list_aux_def)
  have surj: "\<forall>t m. (t, m) \<in> ?s \<longrightarrow> (\<exists>k. unpack_int t = Some k)"
    using assms(1) LInt by(auto simp:int_mset_conv_def valid_list_aux_def type_restr_mset_def unpack_int_def split:event_data.splits)
  have ord_preserve: " \<forall>t1 m1 t2 m2. (t1, m1) \<in> ?s \<and> (t2, m2) \<in> ?s \<longrightarrow> c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_int t1)) (the (unpack_int t2))"
    using assms(1) LInt int_cmp_eq[OF c_def] by(auto simp:valid_list_aux_def type_restr_mset_def image_iff)
  note sort_eq = sort_flatten_mset_eq[OF c_def valid valid_finite_group_mset[OF assms(2)] surj ord_preserve]
  have "set (x # xs) \<subseteq> range EInt"
  proof -
    have "type_restr_mset EInt ?s" using assms(1) LInt by (simp add: valid_list_aux_def)
    moreover have "finite ?s" using assms(2) by simp
    ultimately have "set (flatten_multiset ?s) \<subseteq> range EInt"
      by (intro flatten_multiset_range) (auto simp only: type_restr_mset_def)
    then show ?thesis unfolding assms(3) .
  qed
  then have type_restr: "x \<in> range EInt" "set xs \<subseteq> range EInt" by auto
  have "sorted_treelist (sort_treelist x1)" by(transfer) (metis sorted_sort)
  moreover obtain x' xs' where unpack_def: "map (\<lambda>a. the (unpack_int a)) (x # xs) = x' # xs'" "x' = the (unpack_int x)" "xs' = map (\<lambda>a. the (unpack_int a)) xs" by force
  have "sorted (map (\<lambda>a. the (unpack_int a)) (x # xs))" unfolding sort_eq[unfolded assms(3), symmetric] by (transfer; simp)
  then have *: "sorted (x' # xs')" unfolding unpack_def(1)[symmetric] unpack_def(2-3) by auto
  show ?thesis unfolding LInt get_edata_list.simps 
    using sort_eq[unfolded assms(3) unpack_def(1)] sorted_foldl_max[OF *, symmetric]  unpack_foldl_max_eq_int[OF type_restr] unfolding unpack_def(2-3) by transfer auto
next
  case (LString x2)
  then have valid: "valid_list_aux' x2 (mset_conv unpack_string ?s)" 
    using assms(1) by(auto simp:str_mset_conv_def valid_list_aux_def)
  have surj: "\<forall>t m. (t, m) \<in> ?s \<longrightarrow> (\<exists>k. unpack_string t = Some k)"
    using assms(1) LString by(auto simp:str_mset_conv_def valid_list_aux_def type_restr_mset_def unpack_string_def split:event_data.splits)
  have ord_preserve: " \<forall>t1 m1 t2 m2. (t1, m1) \<in> ?s \<and> (t2, m2) \<in> ?s \<longrightarrow> c t1 t2 = comp_of_ords (\<le>) (<) (the (unpack_string t1)) (the (unpack_string t2))"
    using assms(1) LString str_cmp_eq[OF c_def] by(auto simp:valid_list_aux_def type_restr_mset_def image_iff)
  note sort_eq = sort_flatten_mset_eq[OF c_def valid valid_finite_group_mset[OF assms(2)] surj ord_preserve]
  have "set (x # xs) \<subseteq> range EString"
  proof -
    have "type_restr_mset EString ?s" using assms(1) LString by (simp add: valid_list_aux_def)
    moreover have "finite ?s" using assms(2) by simp
    ultimately have "set (flatten_multiset ?s) \<subseteq> range EString"
      by (intro flatten_multiset_range) (auto simp only: type_restr_mset_def)
    then show ?thesis unfolding assms(3) .
  qed
  then have type_restr: "x \<in> range EString" "set xs \<subseteq> range EString" by auto
  have "sorted_treelist (sort_treelist x2)" by(transfer) (metis sorted_sort)
  moreover obtain x' xs' where unpack_def: "map (\<lambda>a. the (unpack_string a)) (x # xs) = x' # xs'" "x' = the (unpack_string x)" "xs' = map (\<lambda>a. the (unpack_string a)) xs" by force
  have "sorted (map (\<lambda>a. the (unpack_string a)) (x # xs))" unfolding sort_eq[unfolded assms(3), symmetric] by (transfer; simp)
  then have *: "sorted (x' # xs')" unfolding unpack_def(1)[symmetric] unpack_def(2-3) by auto
  show ?thesis unfolding LString get_edata_list.simps 
    using sort_eq[unfolded assms(3) unpack_def(1)] sorted_foldl_max[OF *, symmetric]  unpack_foldl_max_eq_str[OF type_restr] unfolding unpack_def(2-3) by transfer auto
qed
qed

lemma finite_group_mset: "finite X \<Longrightarrow> finite_multiset (group_multiset k b cs f X)"
  unfolding finite_multiset_def by (auto simp add: ecard_def)

lemma valid_result_maggaux_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> aux X"
  shows "result_maggaux \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> aux
       = eval_aggargs \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr> X"
proof (cases "g0 \<and> X = {}")
  case True
  then show ?thesis using valid_before 
    by (cases aux) (simp add:empty_table_def eval_aggargs_def eval_agg_def split:prod.splits)+ 
next
  case False
  then have not_singleton: "\<not>(g0 \<and> X = {})" by auto
  let ?args = "\<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"
  define b where "b = length tys"
  have finite_X: "finite X" using valid_before by auto
  have g0: "aggargs_g0 ?args = g0" by auto
  show ?thesis using valid_before
  proof(induction aux)
    case (CntAux m)
    then obtain y0 where agg_type: "\<omega> = (Formula.Agg_Cnt, y0)" using CntAux by auto (metis prod.collapse)
    have not_singleton_map: "(g0 \<and> Mapping.keys m = {}) = False" using not_singleton CntAux by auto
    show ?case
    proof (rule set_eqI, rule iffI)
      fix x
      assume "x \<in> result_maggaux ?args (CntAux m)"
      then obtain k n where x_def: "Mapping.lookup m k = Some n" "x = EInt (of_nat n) # k"
        using not_singleton_map CntAux by(simp add:agg_type get_map_result_def) blast
      let ?list = "flatten_multiset (group_multiset k b cs f X)"
      have k_in: "k \<in> (agg_key b cs) ` X" using CntAux x_def b_def by (simp add: keys_is_none_rep) 
      moreover have "?list \<noteq> []"
        using flatten_multiset_not_empty[of _ b cs f m X k] CntAux finite using b_def calculation by simp blast
      moreover have "n = length ?list" 
        using length_mset_eq[OF _ valid_finite_group_mset[OF finite_X], of k b cs f Some, symmetric]
        x_def CntAux k_in b_def by auto
      ultimately have "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" 
        using agg_type x_def b_def finite_group_mset[OF finite_X]
        by(cases ?list) (auto) 
      then show "x \<in> eval_aggargs ?args X" 
        using k_in b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def)
    next
      fix x
      assume "x \<in> eval_aggargs ?args X"
      then obtain k where x_def: "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" "k \<in> agg_key b cs ` X"
        using b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def) blast
      let ?list = "flatten_multiset (group_multiset k b cs f X)"
      have lookup: "Mapping.lookup m k = Some (length ?list)" 
        using x_def CntAux agg_type length_mset_eq[OF _ valid_finite_group_mset[OF finite_X], of k b cs f Some, symmetric] b_def by(auto)
      moreover have k_in: "k \<in> Mapping.keys m" using x_def(2) CntAux b_def by auto
      moreover have "?list \<noteq> []"
        using flatten_multiset_not_empty[of _ b cs f m X k] CntAux finite x_def b_def by simp blast
      ultimately have "x = (case Mapping.lookup m k of None \<Rightarrow> k | 
                                                         Some n \<Rightarrow> EInt (of_nat n) # k)"
        using CntAux agg_type x_def(1) finite_group_mset[OF finite_X] by(cases ?list) (simp)+
      then show "x \<in> result_maggaux ?args (CntAux m)" using k_in
        by(simp add:not_singleton_map x_def(1) agg_type get_map_result_def lookup rev_image_eqI) 
    qed
  next
    case (RankAux aux)
    then obtain m type where [simp]: "aux = (m, type)" by (meson surj_pair)
    have not_singleton_map: "(g0 \<and> Mapping.keys m = {}) = False" using not_singleton RankAux by auto
    then show ?case 
    proof (cases "fst \<omega> = Formula.Agg_Med")
      case True
      then obtain y0 where agg_type: "\<omega> = (Formula.Agg_Med, y0)" using RankAux by auto (metis prod.collapse)
      let ?med = "\<lambda>l. let u = get_length l;
                          u' = u div 2;
                          aggval = if even u then ((double_of_event_data_agg (get_edata_list l (u' - 1)) + double_of_event_data_agg (get_edata_list l u')) / double_of_int 2)
                                    else double_of_event_data_agg (get_edata_list l u') in
                          EFloat aggval"
      have med_eq: "eval_agg_op \<omega> (group_multiset k b cs f X) = ?med l"
        if valid_list_aux: "valid_list_aux l (group_multiset k b cs f X) type"
          and not_empty: "flatten_multiset (group_multiset k b cs f X) \<noteq> []" for k l
      proof -
        let ?list = "flatten_multiset (group_multiset k b cs f X)"
        have len: "length ?list = get_length l"
          using valid_list_aux_length_eq[OF valid_list_aux finite_X] by simp
        have nth: "?list ! i = get_edata_list l i" if "i < get_length l" for i
          using valid_get_edata_list[OF valid_list_aux valid_finite_group_mset[OF finite_X] _ that] by simp
        have "get_length l \<noteq> 0" using not_empty unfolding len[symmetric] by simp
        then have *: "get_length l div 2 < get_length l" and **: "get_length l div 2 - 1 < get_length l"
          by auto
        have "eval_agg_op \<omega> (group_multiset k b cs f X) =
          EFloat (let u = length ?list; u' = u div 2 in
            if even u then (double_of_event_data_agg (?list ! (u' - 1)) + double_of_event_data_agg (?list ! u')) / double_of_int 2
            else double_of_event_data_agg (?list ! u'))"
          using not_empty finite_group_mset[OF finite_X] by (simp add: agg_type split: list.split)
        also have "\<dots> = ?med l" by (simp only: Let_def len nth[OF *] nth[OF **])
        finally show ?thesis .
      qed
      show ?thesis
      proof (rule set_eqI, rule iffI)
        fix x
        assume x_in: "x \<in> result_maggaux ?args (RankAux aux)"
        obtain k l where x_def: "Mapping.lookup m k = Some l" "x = ?med l # k"
        proof -
          have "x \<in> get_map_result m ?med"
            using x_in not_singleton_map by (simp add: agg_type)
          then obtain k where k: "k \<in> Mapping.keys m"
            and x_k: "x = (case Mapping.lookup m k of Some l \<Rightarrow> ?med l # k | None \<Rightarrow> k)"
            unfolding get_map_result_def by blast
          from k obtain l where l: "Mapping.lookup m k = Some l" by (auto dest: in_keysD)
          show thesis by (rule that[OF l]) (simp add: x_k l)
        qed
        let ?list = "flatten_multiset (group_multiset k b cs f X)"
        have valid_list_aux: "valid_list_aux l (group_multiset k b cs f X) type" using x_def RankAux b_def by(auto simp:keys_is_none_rep split:option.splits) 
        have k_in: "k \<in> (agg_key b cs) ` X" using RankAux x_def b_def by (simp add: keys_is_none_rep) 
        have not_empty: "?list \<noteq> []"
          using flatten_multiset_not_empty[of _ b cs f m X k] RankAux finite using k_in b_def by simp blast
        have "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k"
          using x_def(2) med_eq[OF valid_list_aux not_empty] by simp
        then show "x \<in> eval_aggargs ?args X" 
          using k_in b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def)
      next
        fix x
        assume "x \<in> eval_aggargs ?args X"
        then obtain k where x_def: "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" "k \<in> agg_key b cs ` X"
          using b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def) blast
        then have k_in: "k \<in> Mapping.keys m" using b_def RankAux by auto
        obtain l where lookup: "Mapping.lookup m k = Some l"
          using Mapping.in_keysD[OF k_in] by auto
        then have valid_list_aux: "valid_list_aux l (group_multiset k b cs f X) type" using RankAux k_in b_def by auto
        let ?list = "flatten_multiset (group_multiset k b cs f X)"
        have not_empty: "?list \<noteq> []"
          using flatten_multiset_not_empty[of _ b cs f m X k] b_def RankAux finite x_def by simp blast
        have "x = ?med l # k"
          using x_def(1) med_eq[OF valid_list_aux not_empty] by simp
        then show "x \<in> result_maggaux ?args (RankAux aux)" using k_in lookup
          by(simp add:not_singleton_map x_def(1) agg_type get_map_result_def lookup rev_image_eqI) 
      qed 
    next
      case False
      then have not_med: "fst \<omega> \<noteq> Formula.Agg_Med" by auto
      then show ?thesis
      proof(cases "fst \<omega> = Formula.Agg_Min")
        case True
        then obtain y0 where agg_type: "\<omega> = (Formula.Agg_Min, y0)" using RankAux by auto (metis prod.collapse)
        show ?thesis
        proof (rule set_eqI, rule iffI)
          fix x
          assume "x \<in> result_maggaux ?args (RankAux aux)"
          then have "x \<in> get_map_result m (\<lambda>k. get_edata_list k 0)"
            using not_singleton_map by (simp add: agg_type)
          then obtain k l where x_def: "Mapping.lookup m k = Some l" 
            "x = get_edata_list l 0 # k"
            unfolding get_map_result_def by (auto dest: Mapping.in_keysD)
          let ?list = "flatten_multiset (group_multiset k b cs f X)"
          have valid_list_aux: "valid_list_aux l (group_multiset k b cs f X) type" using x_def RankAux b_def by(auto simp:keys_is_none_rep split:option.splits) 
          have k_in: "k \<in> (agg_key b cs) ` X" using RankAux x_def b_def by (simp add: keys_is_none_rep) 
          have not_empty: "?list \<noteq> []"
            using flatten_multiset_not_empty[of _ b cs f m X k] RankAux finite using k_in b_def by simp blast
          then obtain x' xs' where split: "?list = x' # xs'" by (meson list.exhaust)
          have "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" 
            using valid_list_aux_min[OF valid_list_aux finite_X split] agg_type x_def split finite_group_mset[OF finite_X]
            by(cases ?list) (auto split:list_aux.splits) 
          then show "x \<in> eval_aggargs ?args X" 
            using k_in b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def)
        next
          fix x
          assume "x \<in> eval_aggargs ?args X"
          then obtain k where x_def: "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" "k \<in> agg_key b cs ` X"
            using b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def) blast
          then have k_in: "k \<in> Mapping.keys m" using RankAux b_def by auto
          obtain l where lookup: "Mapping.lookup m k = Some l"
            using Mapping.in_keysD[OF k_in] by auto
          then have valid_list_aux: "valid_list_aux l (group_multiset k b cs f X) type" using b_def RankAux k_in by auto
          let ?list = "flatten_multiset (group_multiset k b cs f X)"
          have not_empty: "?list \<noteq> []"
            using flatten_multiset_not_empty[of _ b cs f m X k] RankAux finite x_def b_def by simp blast
          then obtain x' xs' where split: "?list = x' # xs'" by (meson list.exhaust)
          then have "x = get_edata_list l 0 # k"
            using RankAux agg_type x_def(1) not_empty 
            valid_list_aux_min[OF valid_list_aux finite_X split] finite_group_mset[OF finite_X]
            by(cases ?list) (auto split:list_aux.splits) 
          then show "x \<in> result_maggaux ?args (RankAux aux)" using k_in lookup
            by(simp add:not_singleton_map x_def(1) agg_type get_map_result_def lookup rev_image_eqI) 
        qed 
      next
        case False
        then have "fst \<omega> = Formula.Agg_Max" using not_med RankAux by simp
        then obtain y0 where agg_type: "\<omega> = (Formula.Agg_Max, y0)" by (metis prod.collapse)
        show ?thesis
        proof (rule set_eqI, rule iffI)
          fix x
          assume "x \<in> result_maggaux ?args (RankAux aux)"
          then have "x \<in> get_map_result m (\<lambda>k. get_edata_list k (get_length k - 1))"
            using not_singleton_map by (simp add: agg_type)
          then obtain k l where x_def: "Mapping.lookup m k = Some l" 
            "x = get_edata_list l (get_length l - 1) # k"
            unfolding get_map_result_def by (auto dest: Mapping.in_keysD)
          let ?list = "flatten_multiset (group_multiset k b cs f X)"
          have valid_list_aux: "valid_list_aux l (group_multiset k b cs f X) type" using b_def x_def RankAux by(auto simp:keys_is_none_rep split:option.splits) 
          have k_in: "k \<in> (agg_key b cs) ` X" using RankAux x_def b_def by (simp add: keys_is_none_rep) 
          have not_empty: "?list \<noteq> []"
            using flatten_multiset_not_empty[of _ b cs f m X k] RankAux finite using k_in b_def by simp blast
          then obtain x' xs' where split: "?list = x' # xs'" by (meson list.exhaust)
          have "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" 
            using valid_list_aux_max[OF valid_list_aux finite_X split] agg_type x_def split
                  valid_list_aux_length_eq[OF valid_list_aux finite_X] finite_group_mset[OF finite_X]
            by(cases ?list) (auto  split:list_aux.splits)
          then show "x \<in> eval_aggargs ?args X" 
            using k_in b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def)
        next
          fix x
          assume "x \<in> eval_aggargs ?args X"
          then obtain k where x_def: "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" "k \<in> agg_key b cs ` X"
            using b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def) blast
          then have k_in: "k \<in> Mapping.keys m" using RankAux b_def by auto
          obtain l where lookup: "Mapping.lookup m k = Some l"
            using Mapping.in_keysD[OF k_in] by auto
          then have valid_list_aux: "valid_list_aux l (group_multiset k b cs f X) type" using RankAux k_in b_def by auto
          let ?list = "flatten_multiset (group_multiset k b cs f X)"
          have not_empty: "?list \<noteq> []"
            using flatten_multiset_not_empty[of _ b cs f m X k] RankAux finite x_def b_def by simp blast
          then obtain x' xs' where split: "?list = x' # xs'" by (meson list.exhaust)
          then have "x = get_edata_list l (get_length l - 1) # k"
            using RankAux agg_type x_def(1) not_empty finite_group_mset[OF finite_X]
            valid_list_aux_max[OF valid_list_aux finite_X split] valid_list_aux_length_eq[OF valid_list_aux finite_X]
            by(cases ?list) (auto split:list_aux.splits) 
          then show "x \<in> result_maggaux ?args (RankAux aux)" using k_in lookup
            by(simp add:not_singleton_map x_def(1) agg_type get_map_result_def lookup rev_image_eqI) 
        qed 
      qed
    qed
  next
    case (SumAux m)
    then show ?case
    proof (cases "fst \<omega> = Formula.Agg_Sum")
      case True
      then obtain y0 where agg_type: "\<omega> = (Formula.Agg_Sum, y0)" using SumAux by auto (metis prod.collapse)
      have not_singleton_map: "(g0 \<and> Mapping.keys m = {}) = False" using not_singleton SumAux by auto
      show ?thesis
      proof (rule set_eqI, rule iffI)
        fix x
        assume "x \<in> result_maggaux ?args (SumAux m)"
        then obtain k s n where x_def: "Mapping.lookup m k = Some(n, s)" "x = EInt s # k"
          using not_singleton_map SumAux by(simp add:agg_type get_map_result_def) blast
        let ?list = "flatten_multiset (group_multiset k b cs f X)"
        have type_restr: "\<forall>t m. (t, m) \<in> group_multiset k b cs f X \<longrightarrow> t \<in> range EInt" using SumAux agg_type by(auto simp:type_restr_def)
        have k_in: "k \<in> (agg_key b cs) ` X" using SumAux x_def b_def by (simp add: keys_is_none_rep) 
        have not_empty: "?list \<noteq> []"
          using flatten_multiset_not_empty[of _ b cs f m X k] SumAux finite using k_in b_def by simp blast
        then obtain x' xs' where list_split: "?list = x' # xs'" using min_list.cases by blast
        then have "EInt s = foldl (+) x' xs'"  
          using x_def k_in SumAux False foldl_int_eq[OF type_restr valid_finite_group_mset[OF finite_X, of k b cs f], of x' xs'] using b_def by simp
        then have "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" using agg_type x_def not_empty list_split finite_group_mset[OF finite_X]
          by(cases ?list) auto
        then show "x \<in> eval_aggargs ?args X" 
          using k_in b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def)
      next
        fix x
        assume "x \<in> eval_aggargs ?args X"
        then obtain k where x_def: "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" "k \<in> agg_key b cs ` X"
          using b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def) blast
        let ?list = "flatten_multiset (group_multiset k b cs f X)"
        have type_restr: "\<forall>t m. (t, m) \<in> group_multiset k b cs f X \<longrightarrow> t \<in> range EInt" using SumAux agg_type by(auto simp:type_restr_def)
        then have "(\<And>t m. (t, m) \<in> group_multiset k b cs f X \<longrightarrow> unpack_int t \<in> range Some)" by(auto simp:unpack_int_def split:event_data.splits)
        then have lookup: "Mapping.lookup m k = Some (length ?list, fold_mset (+) 0 (int_mset_conv (group_multiset k b cs f X)))" 
          using x_def SumAux agg_type length_mset_eq[OF _ valid_finite_group_mset[OF finite_X], of k b cs f unpack_int, symmetric] b_def
          by(auto simp:int_mset_conv_def)
        have k_in: "k \<in> Mapping.keys m" using x_def(2) SumAux b_def by auto
        have not_empty: "?list \<noteq> []"
          using flatten_multiset_not_empty[of _ b cs f m X k] SumAux finite x_def b_def by simp blast
        then obtain x' xs' where list_split: "?list = x' # xs'" using min_list.cases by blast
        then have "x = (case Mapping.lookup m k of None \<Rightarrow> k | 
                                                         Some (n, s) \<Rightarrow> EInt s # k)"
          using SumAux agg_type x_def(1) not_empty lookup finite_group_mset[OF finite_X]
          foldl_int_eq[OF type_restr valid_finite_group_mset[OF finite_X, of k b cs f], of x' xs'] by(cases ?list) (simp)+
        then show "x \<in> result_maggaux ?args (SumAux m)" using k_in
          by(simp add:not_singleton_map x_def(1) agg_type get_map_result_def lookup rev_image_eqI) 
      qed 
    next
      case False
      then obtain y0 where agg_type: "\<omega> = (Formula.Agg_Avg, y0)" using SumAux by auto (metis prod.collapse)
      have not_singleton_map: "(g0 \<and> Mapping.keys m = {}) = False" using not_singleton SumAux by auto
      show ?thesis
      proof (rule set_eqI, rule iffI)
        fix x
        assume "x \<in> result_maggaux ?args (SumAux m)"
        then obtain k s n where x_def: "Mapping.lookup m k = Some(n, s)" "x = EFloat(double_of_integer s / double_of_int n) # k"
          using not_singleton_map SumAux by(simp add:agg_type get_map_result_def) blast
        let ?list = "flatten_multiset (group_multiset k b cs f X)"
        have type_restr: "\<forall>t m. (t, m) \<in> group_multiset k b cs f X \<longrightarrow> t \<in> range EInt" using SumAux agg_type by(auto simp:type_restr_def)
        then have *: "(\<And>t m. (t, m) \<in> group_multiset k b cs f X \<longrightarrow> unpack_int t \<in> range Some)" by(auto simp:unpack_int_def split:event_data.splits)
        have k_in: "k \<in> (agg_key b cs) ` X" using SumAux x_def b_def by (simp add: keys_is_none_rep) 
        have n_len: "n = length ?list" 
        using length_mset_eq[OF _ valid_finite_group_mset[OF finite_X], of k b cs f unpack_int, symmetric] *
        x_def SumAux k_in b_def by (auto simp:int_mset_conv_def)
        have not_empty: "?list \<noteq> []"
          using flatten_multiset_not_empty[of _ b cs f m X k] SumAux finite using k_in b_def by simp blast
        then obtain x' xs' where list_split: "?list = x' # xs'" using min_list.cases by blast
        then have "foldl (+) x' xs' = EInt s"  
          using x_def k_in SumAux False foldl_int_eq[OF type_restr valid_finite_group_mset[OF finite_X, of k b cs f], of x' xs'] b_def by simp
        then have "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" using agg_type x_def not_empty list_split n_len
          finite_group_mset[OF finite_X] by(cases ?list) auto
        then show "x \<in> eval_aggargs ?args X" 
          using k_in b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def)
      next
        fix x
        assume "x \<in> eval_aggargs ?args X"
        then obtain k where x_def: "x = eval_agg_op \<omega> (group_multiset k b cs f X) # k" "k \<in> agg_key b cs ` X"
          using b_def by(simp add:eval_aggargs_def eval_agg_def not_singleton empty_table_def) blast
        let ?list = "flatten_multiset (group_multiset k b cs f X)"
        have type_restr: "\<forall>t m. (t, m) \<in> group_multiset k b cs f X \<longrightarrow> t \<in> range EInt" using SumAux agg_type by(auto simp:type_restr_def)
        then have "(\<And>t m. (t, m) \<in> group_multiset k b cs f X \<longrightarrow> unpack_int t \<in> range Some)" by(auto simp:unpack_int_def split:event_data.splits)
        then have lookup: "Mapping.lookup m k = Some (length ?list, fold_mset (+) 0 (int_mset_conv (group_multiset k b cs f X)))" 
          using x_def SumAux agg_type length_mset_eq[OF _ valid_finite_group_mset[OF finite_X], of k b cs f unpack_int, symmetric] 
          b_def by(auto simp:int_mset_conv_def)
        have k_in: "k \<in> Mapping.keys m" using x_def(2) SumAux b_def by auto
        have not_empty: "?list \<noteq> []"
          using flatten_multiset_not_empty[of _ b cs f m X k] SumAux finite x_def b_def by simp blast
        then obtain x' xs' where list_split: "?list = x' # xs'" using min_list.cases by blast
        then have "x = (case Mapping.lookup m k of None \<Rightarrow> k | 
                                                         Some (n, s) \<Rightarrow> EFloat (double_of_event_data_agg (EInt s) / double_of_int n) # k)"
          using SumAux agg_type x_def(1) not_empty lookup finite_group_mset[OF finite_X] b_def
          foldl_int_eq[OF type_restr valid_finite_group_mset[OF finite_X, of k b cs f], of x' xs'] by(cases ?list) (simp del:double_of_event_data_agg.simps)+
        then show "x \<in> result_maggaux ?args (SumAux m)" using k_in
          by(simp add:not_singleton_map x_def(1) agg_type get_map_result_def lookup rev_image_eqI) 
      qed 
    qed
  qed
qed

lemma valid_result_maggaux: "valid_maggaux args aux X \<Longrightarrow> result_maggaux args aux = eval_aggargs args X"
  using valid_result_maggaux_unfolded by (cases args) fast 

end
