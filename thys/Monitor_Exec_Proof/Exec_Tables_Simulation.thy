(*<*)
theory Exec_Tables_Simulation
  imports "Monitor_Exec.Exec_Tables" "Monitor_Impl_Proof.Monitor_Instance_Valid"
begin
(*>*)

section \<open>Correctness of tables over ascending columns\<close>

subsection \<open>Short form and short join\<close>

lemma restrict_inv':
  assumes "eframe ks cs" "length d = length cs"
  shows "restrict cs ks (restrict ks cs d) = d"
  using assms eframeD(4)[OF assms(1)]
  by (simp add: eframe_def restrict_restrict restrict_idle wf_tuple_def)

lemma etabc_in_iff:
  "eframe ks cs \<Longrightarrow> table ks T \<Longrightarrow> wf_tuple ks x \<Longrightarrow> (restrict cs ks x \<in> etabc ks cs T) = (x \<in> T)"
  using inj_on_restrict[of ks cs] by (auto simp: etabc_def table_def inj_on_def)

lemma table_etabc: "table cs (etabc ks cs T)"
  by (auto simp: table_def wf_tuple_def etabc_def)

lemma etabw_dtabc: "eframe ks cs \<Longrightarrow> table ks T \<Longrightarrow> etabw ks cs (etabc ks cs T) = T"
  by (force simp: etabw_def etabc_def table_def restrict_inv image_image)

lemma etabc_empty_iff: "(etabc ks cs T = {}) = (T = {})"
  by (auto simp: etabc_def)

lemma etabc_Un_img: "etabc ks cs (A \<union> B) = etabc ks cs A \<union> etabc ks cs B"
  by (auto simp: etabc_def)

lemma finite_etabc: "finite T \<Longrightarrow> finite (etabc ks cs T)"
  by (simp add: etabc_def)

lemma etabc_same: "distinct cs \<Longrightarrow> table cs T \<Longrightarrow> etabc cs cs T = T"
  by (force simp: etabc_def table_def restrict_idle)

lemma ejoin1_all_MRgt: "ejoin1 (map (\<lambda>_. MRgt) ds) xs (map g ds) = Some (map g ds)"
  by (induct ds arbitrary: xs) auto

lemma ejoin1_all_MLft: "ejoin1 (mrg_plan cs []) (map f cs) ys = Some (map f cs)"
  by (induct cs arbitrary: ys) auto

lemma set_merge_cols: "set (merge_cols cs ds) = set cs \<union> set ds"
  by (induct cs ds rule: merge_cols.induct) auto

lemma sorted_merge_cols:
  "sorted_wrt (<) cs \<Longrightarrow> sorted_wrt (<) ds \<Longrightarrow> sorted_wrt (<) (merge_cols cs ds)"
  by (induct cs ds rule: merge_cols.induct) (auto simp: set_merge_cols)

lemma ejoin1_mrg_plan:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow>
   ejoin1 (mrg_plan cs1 cs2) (map f cs1) (map g cs2) =
     (if \<forall>c \<in> set cs1 \<inter> set cs2. f c = g c
      then Some (map (\<lambda>c. if c \<in> set cs1 then f c else g c) (merge_cols cs1 cs2))
      else None)"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: ejoin1_all_MRgt cong: map_cong)
next
  case (2 c cs)
  then show ?case by (simp add: ejoin1_all_MLft merge_cols_Nil2 cong: map_cong)
next
  case (3 c cs d ds)
  have s1: "sorted_wrt (<) cs" and hc: "\<forall>x \<in> set cs. c < x"
    and s2: "sorted_wrt (<) ds" and hd: "\<forall>x \<in> set ds. d < x"
    using 3(4,5) by auto
  consider (lt) "c < d" | (gt) "d < c" | (eq) "c = d" by force
  then show ?case
  proof cases
    case lt
    have ni: "c \<notin> set cs" "c \<notin> set ds" "c \<noteq> d" using hc hd lt by auto
    show ?thesis using 3(1)[OF lt s1 3(5)] lt ni hc hd
      by (auto simp: set_merge_cols cong: map_cong)
  next
    case gt
    have ni: "d \<notin> set cs" "d \<notin> set ds" "c \<noteq> d" using hc hd gt by auto
    show ?thesis using 3(2)[OF _ gt 3(4) s2] gt ni hc hd
      by (auto simp: set_merge_cols cong: map_cong)
  next
    case eq
    have ni: "c \<notin> set cs" "c \<notin> set ds" using hc hd eq by auto
    show ?thesis using 3(3)[OF _ _ s1 s2] eq ni hc hd
      by (auto simp: set_merge_cols cong: map_cong)
  qed
qed

subsection \<open>Agreement with the kernel's join\<close>

lemma eframe_merge:
  "eframe ks1 cs1 \<Longrightarrow> eframe ks2 cs2 \<Longrightarrow> eframe (cols_union ks1 ks2) (merge_cols cs1 cs2)"
  by (auto simp: eframe_def sorted_merge_cols set_merge_cols)

lemma tup_get_join1:
  assumes "wf_tuple ks1 x" "join1 ks1 ks2 (x, y) = Some z" "c \<in> set ks1 \<union> set ks2"
  shows "tup_get (cols_union ks1 ks2) z c = (if c \<in> set ks1 then tup_get ks1 x c else tup_get ks2 y c)"
  using assms
  by (auto simp: join1.simps cols_union_def tup_get_append tup_get_restrict split: if_splits)

lemma join1_iff:
  "join1 ks1 ks2 (x, y) \<noteq> None \<longleftrightarrow> (\<forall>c \<in> set ks1 \<inter> set ks2. tup_get ks1 x c = tup_get ks2 y c)"
  by (simp add: join1.simps)

lemma ejoin1_join1:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2"
    and w1: "wf_tuple ks1 x"
  shows "ejoin1 (mrg_plan cs1 cs2) (restrict cs1 ks1 x) (restrict cs2 ks2 y)
       = map_option (restrict (merge_cols cs1 cs2) (cols_union ks1 ks2)) (join1 ks1 ks2 (x, y))"
proof -
  note s1 = eframeD(2)[OF f1] and s2 = eframeD(2)[OF f2]
  have set1: "set cs1 = set ks1" and set2: "set cs2 = set ks2"
    using f1 f2 by (simp_all add: eframe_def)
  show ?thesis
  proof (cases "join1 ks1 ks2 (x, y)")
    case None
    then show ?thesis
      using join1_iff[of ks1 ks2 x y]
      by (simp add: restrict_map ejoin1_mrg_plan[OF s1 s2] set1 set2)
  next
    case (Some z)
    then have ag: "\<forall>c \<in> set ks1 \<inter> set ks2. tup_get ks1 x c = tup_get ks2 y c"
      using join1_iff[of ks1 ks2 x y] by simp
    have "map (\<lambda>c. if c \<in> set cs1 then tup_get ks1 x c else tup_get ks2 y c) (merge_cols cs1 cs2)
        = map (tup_get (cols_union ks1 ks2) z) (merge_cols cs1 cs2)"
      using tup_get_join1[OF w1 Some] by (auto simp: set_merge_cols set1 set2)
    then show ?thesis
      using Some ag by (simp add: restrict_map ejoin1_mrg_plan[OF s1 s2] set1 set2)
  qed
qed

lemma etabc_join:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2"
    and t1: "table ks1 T"
  shows "etabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T True ks2 T')
       = (\<Union>a \<in> etabc ks1 cs1 T. \<Union>b \<in> etabc ks2 cs2 T'.
            set_option (ejoin1 (mrg_plan cs1 cs2) a b))"
proof -
  have key: "\<And>a b. a \<in> T \<Longrightarrow>
      ejoin1 (mrg_plan cs1 cs2) (restrict cs1 ks1 a) (restrict cs2 ks2 b)
        = map_option (restrict (merge_cols cs1 cs2) (cols_union ks1 ks2)) (join1 ks1 ks2 (a, b))"
    using t1 by (intro ejoin1_join1[OF f1 f2]) (auto simp: table_def)
  have "etabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T True ks2 T')
      = (\<Union>a \<in> T. \<Union>b \<in> T'. restrict (merge_cols cs1 cs2) (cols_union ks1 ks2) `
           set_option (join1 ks1 ks2 (a, b)))"
    unfolding etabc_def join_True_code by blast
  also have "\<dots> = (\<Union>a \<in> T. \<Union>b \<in> T'. set_option
      (ejoin1 (mrg_plan cs1 cs2) (restrict cs1 ks1 a) (restrict cs2 ks2 b)))"
    by (intro SUP_cong refl) (auto simp: key split: option.splits)
  also have "\<dots> = (\<Union>a \<in> etabc ks1 cs1 T. \<Union>b \<in> etabc ks2 cs2 T'.
      set_option (ejoin1 (mrg_plan cs1 cs2) a b))"
    unfolding etabc_def by blast
  finally show ?thesis .
qed

lemma etabc_restrict:
  assumes "eframe ks cs" "set ks' = set ks" "table ks T"
  shows "etabc ks' cs (restrict ks' ks ` T) = etabc ks cs T"
  using assms by (force simp: etabc_def eframe_def image_image restrict_restrict)

lemma no_right_mrg_plan:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow>
     no_right (mrg_plan cs1 cs2) = (set cs2 \<subseteq> set cs1)"
  by (induct cs1 cs2 rule: mrg_plan.induct) (auto simp: no_right_def list_all_iff)

lemma eproj_mrg_left_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     eproj (mrg_left_key (mrg_plan cs1 cs2)) (map f cs1) = map f cs2"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

lemma eproj_left_key_eq:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2" and sub: "set cs2 \<subseteq> set cs1"
  shows "eproj (mrg_left_key (mrg_plan cs1 cs2)) (restrict cs1 ks1 a)
       = restrict cs2 ks2 (restrict ks2 ks1 a)"
proof -
  have "set cs2 \<subseteq> set ks2" using f2 by (simp add: eframe_def)
  then show ?thesis
    using eproj_mrg_left_key[OF eframeD(2)[OF f1] eframeD(2)[OF f2] sub, of "tup_get ks1 a"]
    by (simp add: restrict_map[symmetric] restrict_restrict)
qed

lemma join_cond_eq: "join_cond pos t v = ((v \<in> t) = pos)"
  by (cases pos) auto

lemma join_sub_eq:
  assumes "distinct ks1" "distinct ks2" "table ks1 T" "table ks2 T'" "set ks2 \<subseteq> set ks1"
  shows "join ks1 T pos ks2 T' = {a \<in> T. (restrict ks2 ks1 a \<in> T') = pos}"
  using join_sub[OF assms] by (simp add: join_cond_eq)

text \<open>This covers the anti-join of @{text "\<phi> AND NOT \<psi>"} and the intersection over equal
  columns.\<close>

theorem esemi_join:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2" and sub: "set cs2 \<subseteq> set cs1"
    and t1: "table ks1 T" and t2: "table ks2 T'"
  shows "esemi (mrg_left_key (mrg_plan cs1 cs2)) pos (etabc ks1 cs1 T) (etabc ks2 cs2 T')
       = etabc ks1 cs1 (join ks1 T pos ks2 T')"
proof -
  have subk: "set ks2 \<subseteq> set ks1" using f1 f2 sub by (simp add: eframe_def)
  have "join ks1 T pos ks2 T' = {a \<in> T. (restrict ks2 ks1 a \<in> T') = pos}"
    by (rule join_sub_eq[OF eframeD(1)[OF f1] eframeD(1)[OF f2] t1 t2 subk])
  moreover have "\<And>a. (eproj (mrg_left_key (mrg_plan cs1 cs2)) (restrict cs1 ks1 a)
      \<in> etabc ks2 cs2 T') = (restrict ks2 ks1 a \<in> T')"
    unfolding eproj_left_key_eq[OF f1 f2 sub] by (rule etabc_in_iff[OF f2 t2]) simp
  ultimately show ?thesis
    unfolding esemi_def etabc_def by auto
qed

subsection \<open>Joins of special shapes\<close>

lemma etabc_Int:
  assumes f: "eframe ks cs" and t1: "table ks T" and t2: "table ks T'"
  shows "etabc ks cs (T \<inter> T') = etabc ks cs T \<inter> etabc ks cs T'"
proof (intro equalityI subsetI)
  fix z assume "z \<in> etabc ks cs T \<inter> etabc ks cs T'"
  then obtain a a' where a: "a \<in> T" "a' \<in> T'" "z = restrict cs ks a" "z = restrict cs ks a'"
    by (auto simp: etabc_def)
  then have "a = a'"
    using restrict_inv[OF f, of a] restrict_inv[OF f, of a'] t1 t2 by (auto simp: table_def)
  then show "z \<in> etabc ks cs (T \<inter> T')" using a by (auto simp: etabc_def)
qed (auto simp: etabc_def)

lemma etabc_Diff:
  assumes f: "eframe ks cs" and t1: "table ks T" and t2: "table ks T'"
  shows "etabc ks cs (T - T') = etabc ks cs T - etabc ks cs T'"
proof (intro equalityI subsetI)
  fix z assume "z \<in> etabc ks cs (T - T')"
  then obtain a where a: "a \<in> T" "a \<notin> T'" "z = restrict cs ks a"
    by (auto simp: etabc_def)
  have "z \<notin> etabc ks cs T'"
  proof
    assume "z \<in> etabc ks cs T'"
    then obtain a' where a': "a' \<in> T'" "z = restrict cs ks a'"
      by (auto simp: etabc_def)
    have wa: "wf_tuple ks a" using t1 a(1) by (auto simp: table_def)
    have wa': "wf_tuple ks a'" using t2 a'(1) by (auto simp: table_def)
    have "a = a'"
      using restrict_inv[OF f wa] restrict_inv[OF f wa'] a(3) a'(2) by simp
    then show False
      using a a'(1) by simp
  qed
  then show "z \<in> etabc ks cs T - etabc ks cs T'"
    using a by (auto simp: etabc_def)
next
  fix z assume "z \<in> etabc ks cs T - etabc ks cs T'"
  then show "z \<in> etabc ks cs (T - T')"
    by (auto simp: etabc_def)
qed

lemma mrg_plan_self: "mrg_plan cs cs = map (\<lambda>_. MBth) cs"
  by (induct cs) auto

lemma eproj_all_True: "eproj (mrg_left_key (map (\<lambda>_. MBth) cs)) xs = take (length cs) xs"
  by (induct cs arbitrary: xs; case_tac xs) auto

theorem etabc_join_eq:
  assumes f1: "eframe ks1 cs" and f2: "eframe ks2 cs" and t1: "table ks1 T" and t2: "table ks2 T'"
  shows "(if pos then etabc ks1 cs T \<inter> etabc ks2 cs T' else etabc ks1 cs T - etabc ks2 cs T')
       = etabc ks1 cs (join ks1 T pos ks2 T')"
proof -
  have p: "eproj (mrg_left_key (mrg_plan cs cs)) (restrict cs ks a) = restrict cs ks a"
    for ks and a :: "'a list"
    by (simp add: mrg_plan_self eproj_all_True)
  have "esemi (mrg_left_key (mrg_plan cs cs)) pos (etabc ks1 cs T) (etabc ks2 cs T')
      = (if pos then etabc ks1 cs T \<inter> etabc ks2 cs T' else etabc ks1 cs T - etabc ks2 cs T')"
    unfolding esemi_def by (auto simp: etabc_def p)
  then show ?thesis
    using esemi_join[OF f1 f2 subset_refl t1 t2, of pos] by simp
qed

lemma etabc_Nil_cols:
  assumes "table [] T'"
  shows "etabc [] [] T' = T'"
  using etabc_same[of "[]" T'] assms by simp

theorem etabc_join_no_cols:
  assumes f1: "eframe ks1 cs" and t1: "table ks1 T" and t2: "table [] T'"
  shows "(if pos = ([] \<in> etabc [] [] T') then etabc ks1 cs T else {})
       = etabc ks1 cs (join ks1 T pos [] T')"
proof -
  have "join ks1 T pos [] T' = {a \<in> T. ([] \<in> T') = pos}"
    using join_sub_eq[of ks1 "[]" T T' pos] eframeD(1)[OF f1] t1 t2 by simp
  then show ?thesis using etabc_Nil_cols[OF t2] by (auto simp: etabc_def)
qed

lemma mrg_plan_Nil2: "mrg_plan cs [] = map (\<lambda>_. MLft) cs"
  by (induct cs) auto

lemma mrg_plan_swap: "map mrg_swap (mrg_plan cs1 cs2) = mrg_plan cs2 cs1"
  by (induct cs1 cs2 rule: mrg_plan.induct) (auto simp: mrg_plan_Nil2)

lemma mrg_right_key_swap: "mrg_right_key p = mrg_left_key (map mrg_swap p)"
  by (induct p rule: mrg_right_key.induct) auto

lemma no_left_swap: "no_left p = no_right (map mrg_swap p)"
  by (induct p) (auto simp: no_left_def no_right_def elim: mrg_swap.elims)

lemma no_left_mrg_plan:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow>
     no_left (mrg_plan cs1 cs2) = (set cs1 \<subseteq> set cs2)"
  by (simp add: no_left_swap mrg_plan_swap no_right_mrg_plan)

lemma eproj_mrg_right_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs1 \<subseteq> set cs2 \<Longrightarrow>
     eproj (mrg_right_key (mrg_plan cs1 cs2)) (map g cs2) = map g cs1"
  using eproj_mrg_left_key[of cs2 cs1] by (simp add: mrg_right_key_swap mrg_plan_swap)

lemma eproj_right_key_eq:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2" and sub: "set cs1 \<subseteq> set cs2"
  shows "eproj (mrg_right_key (mrg_plan cs1 cs2)) (restrict cs2 ks2 b)
       = restrict cs1 ks1 (restrict ks1 ks2 b)"
proof -
  have "set cs1 \<subseteq> set ks1" using f1 by (simp add: eframe_def)
  then show ?thesis
    using eproj_mrg_right_key[OF eframeD(2)[OF f1] eframeD(2)[OF f2] sub, of "tup_get ks2 b"]
    by (simp add: restrict_map[symmetric] restrict_restrict)
qed

lemma merge_cols_sub_left:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     merge_cols cs1 cs2 = cs1"
  by (rule strict_sorted_equal) (auto simp: set_merge_cols sorted_merge_cols)

lemma merge_cols_sub_right:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs1 \<subseteq> set cs2 \<Longrightarrow>
     merge_cols cs1 cs2 = cs2"
  by (rule strict_sorted_equal) (auto simp: set_merge_cols sorted_merge_cols)

theorem esup_join:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2" and sub: "set cs1 \<subseteq> set cs2"
    and t1: "table ks1 T" and t2: "table ks2 T'"
  shows "Set.filter (\<lambda>b. eproj (mrg_right_key (mrg_plan cs1 cs2)) b \<in> etabc ks1 cs1 T)
           (etabc ks2 cs2 T')
       = etabc (cols_union ks1 ks2) cs2 (join ks1 T True ks2 T')"
proof -
  let ?U = "cols_union ks1 ks2"
  have subk: "set ks1 \<subseteq> set ks2" using f1 f2 sub by (simp add: eframe_def)
  have j: "join ks1 T True ks2 T' = restrict ?U ks2 ` {b \<in> T'. restrict ks1 ks2 b \<in> T}"
    by (rule join_sub'[OF eframeD(1)[OF f1] eframeD(1)[OF f2] t1 t2 subk])
  have c2: "set cs2 \<subseteq> set ?U" using f2 by (auto simp: eframe_def)
  have mem: "\<And>b. (eproj (mrg_right_key (mrg_plan cs1 cs2)) (restrict cs2 ks2 b) \<in> etabc ks1 cs1 T)
      = (restrict ks1 ks2 b \<in> T)"
    unfolding eproj_right_key_eq[OF f1 f2 sub] by (rule etabc_in_iff[OF f1 t1]) simp
  have e: "\<And>x. restrict cs2 ?U (restrict ?U ks2 x) = restrict cs2 ks2 x"
    by (rule restrict_restrict[OF c2])
  show ?thesis
    unfolding j etabc_def[of ks2 cs2] etabc_def[of ?U cs2] image_image e
    using mem by auto
qed

lemma etabc_join_sub_res:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2" and sub: "set cs2 \<subseteq> set cs1"
  shows "cols_union ks1 ks2 = ks1" "merge_cols cs1 cs2 = cs1"
proof -
  show "cols_union ks1 ks2 = ks1"
    using f1 f2 sub by (intro cols_union_subset) (simp add: eframe_def)
  show "merge_cols cs1 cs2 = cs1"
    by (rule merge_cols_sub_left[OF eframeD(2)[OF f1] eframeD(2)[OF f2] sub])
qed

subsection \<open>General join through an index\<close>

lemma length_filter_mrg_plan_left: "length (filter (\<lambda>m. m \<noteq> MRgt) (mrg_plan cs1 cs2)) = length cs1"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

lemma length_filter_mrg_plan_right: "length (filter (\<lambda>m. m \<noteq> MLft) (mrg_plan cs1 cs2)) = length cs2"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

lemma ejoin1_dmerge:
  "length a = length (filter (\<lambda>m. m \<noteq> MRgt) p) \<Longrightarrow>
   length b = length (filter (\<lambda>m. m \<noteq> MLft) p) \<Longrightarrow>
   ejoin1 p a b = (if eproj (mrg_left_key p) a = eproj (mrg_right_key p) b
                   then Some (emerge p a b) else None)"
proof (induct p arbitrary: a b)
  case (Cons m p)
  show ?case
  proof (cases m)
    case MLft
    then obtain x xs where a: "a = x # xs" using Cons(2) by (cases a) auto
    show ?thesis using Cons(1)[of xs b] Cons(2,3) by (simp add: MLft a)
  next
    case MRgt
    then obtain y ys where b: "b = y # ys" using Cons(3) by (cases b) auto
    show ?thesis using Cons(1)[of a ys] Cons(2,3) by (simp add: MRgt b)
  next
    case MBth
    then obtain x xs where a: "a = x # xs" using Cons(2) by (cases a) auto
    obtain y ys where b: "b = y # ys" using MBth Cons(3) by (cases b) auto
    show ?thesis using Cons(1)[of xs ys] Cons(2,3) by (simp add: MBth a b)
  qed
qed simp

lemma fold_insert_image: "fold (\<lambda>b acc. Set.insert (f b) acc) l acc = f ` set l \<union> acc"
  by (induct l arbitrary: acc) auto

lemma bucket_gindex_step:
  "bucket (gindex_step msk x m) k = (if eproj msk x = k then x # bucket m k else bucket m k)"
  by (auto simp: bucket_def gindex_step_def Let_def Mapping.lookup_update'
      split: option.splits)

lemma gindex_fold_lookup:
  "set (bucket (fold (gindex_step msk) xs m) k)
   = {b \<in> set xs. eproj msk b = k} \<union> set (bucket m k)"
  by (induct xs arbitrary: m) (auto simp: bucket_gindex_step)

lemma gindex_lookup:
  assumes "set (csl B) = B"
  shows "set (bucket (gindex msk B) k) = {b \<in> B. eproj msk b = k}"
  using gindex_fold_lookup[of msk "csl B" Mapping.empty k] assms
  by (simp add: gindex_def bucket_def)

lemma eprobe_fold:
  "fold (gprobe_step p lk m) xs acc
   = acc \<union> (\<Union>a \<in> set xs. (\<lambda>b. emerge p a b) ` set (bucket m (eproj lk a)))"
  by (induct xs arbitrary: acc)
    (auto simp: gprobe_step_def bucket_def fold_insert_image split: option.splits)

lemma eprobe_l_fold:
  "fold (gprobe_step_l p rk m) ys acc
   = acc \<union> (\<Union>y \<in> set ys. (\<lambda>x. emerge p x y) ` set (bucket m (eproj rk y)))"
  by (induct ys arbitrary: acc)
    (auto simp: gprobe_step_l_def bucket_def fold_insert_image split: option.splits)

lemma ggen_join_eq:
  assumes cA: "set (csl A) = (A :: event_data table)" and cB: "set (csl B) = B"
  shows "ggen_join p lk rk A B
       = {emerge p a b | a b. a \<in> A \<and> b \<in> B \<and> eproj lk a = eproj rk b}"
  by (auto simp: ggen_join_def Let_def eprobe_fold eprobe_l_fold empty_table_def
      gindex_lookup[OF cA] gindex_lookup[OF cB] cA cB) force

lemma set_option_ejoin1:
  "length a = length (filter (\<lambda>m. m \<noteq> MRgt) p) \<Longrightarrow>
   length b = length (filter (\<lambda>m. m \<noteq> MLft) p) \<Longrightarrow>
   set_option (ejoin1 p a b)
     = (if eproj (mrg_left_key p) a = eproj (mrg_right_key p) b then {emerge p a b} else {})"
  by (simp add: ejoin1_dmerge)

lemma set_csl_etabc:
  "finite T \<Longrightarrow> set (csl (etabc ks cs (T :: event_data table))) = etabc ks cs T"
  by (simp add: csl_finite finite_etabc set_csorted_list_of_set_etuple)

theorem etabc_gen_join:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2"
    and t1: "table ks1 (T :: event_data table)" and t2: "table ks2 T'"
    and fT: "finite T" and fT': "finite T'"
  shows "ggen_join (mrg_plan cs1 cs2) (mrg_left_key (mrg_plan cs1 cs2))
           (mrg_right_key (mrg_plan cs1 cs2)) (etabc ks1 cs1 T) (etabc ks2 cs2 T')
       = etabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T True ks2 T')"
proof -
  let ?p = "mrg_plan cs1 cs2"
  have la: "\<And>a. a \<in> etabc ks1 cs1 T \<Longrightarrow> length a = length (filter (\<lambda>m. m \<noteq> MRgt) ?p)"
    by (auto simp: etabc_def length_filter_mrg_plan_left)
  have lb: "\<And>b. b \<in> etabc ks2 cs2 T' \<Longrightarrow> length b = length (filter (\<lambda>m. m \<noteq> MLft) ?p)"
    by (auto simp: etabc_def length_filter_mrg_plan_right)
  have "ggen_join ?p (mrg_left_key ?p) (mrg_right_key ?p) (etabc ks1 cs1 T) (etabc ks2 cs2 T')
      = (\<Union>a \<in> etabc ks1 cs1 T. \<Union>b \<in> etabc ks2 cs2 T'. set_option (ejoin1 ?p a b))"
    unfolding ggen_join_eq[OF set_csl_etabc[OF fT] set_csl_etabc[OF fT']]
    by (auto simp: set_option_ejoin1[OF la lb] split: if_splits)
  also have "\<dots> = etabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T True ks2 T')"
    by (rule etabc_join[OF f1 f2 t1, symmetric])
  finally show ?thesis .
qed

subsection \<open>Binary join of any shape\<close>

text \<open>A negative join needs the right operand's columns among the left's, as the safety of
  @{text "\<phi> AND NOT \<psi>"} provides.\<close>

theorem gbin_join0_join:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2"
    and t1: "table ks1 (T :: event_data table)" and t2: "table ks2 T'"
    and neg: "\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1"
    and fT: "finite T" and fT': "finite T'"
  shows "gbin_join0 (mk_djoin cs1 cs2) (etabc ks1 cs1 T) pos (etabc ks2 cs2 T')
       = etabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T pos ks2 T')"
proof (cases "cs1 = cs2")
  case True
  then have f2': "eframe ks2 cs1" using f2 by simp
  have sub: "set cs2 \<subseteq> set cs1" using True by simp
  have "gbin_join0 (mk_djoin cs1 cs2) (etabc ks1 cs1 T) pos (etabc ks2 cs2 T')
      = (if pos then etabc ks1 cs1 T \<inter> etabc ks2 cs1 T' else etabc ks1 cs1 T - etabc ks2 cs1 T')"
    using True by (simp add: mk_djoin_def)
  also have "\<dots> = etabc ks1 cs1 (join ks1 T pos ks2 T')"
    by (rule etabc_join_eq[OF f1 f2' t1 t2])
  finally show ?thesis using etabc_join_sub_res[OF f1 f2 sub] by simp
next
  case ne: False
  note s1 = eframeD(2)[OF f1] and s2 = eframeD(2)[OF f2]
  show ?thesis
  proof (cases "cs2 = []")
    case True
    then have k2: "ks2 = []" using f2 by (simp add: eframe_def)
    then have tt: "table [] T'" using t2 by simp
    have "gbin_join0 (mk_djoin cs1 cs2) (etabc ks1 cs1 T) pos (etabc ks2 cs2 T')
        = (if pos = ([] \<in> etabc [] [] T') then etabc ks1 cs1 T else {})"
      using ne True k2 by (simp add: mk_djoin_def empty_table_def)
    also have "\<dots> = etabc ks1 cs1 (join ks1 T pos [] T')" by (rule etabc_join_no_cols[OF f1 t1 tt])
    finally show ?thesis using True k2 by (simp add: merge_cols_Nil2)
  next
    case ne2: False
    let ?p = "mrg_plan cs1 cs2"
    show ?thesis
    proof (cases "no_right ?p")
      case True
      then have sub: "set cs2 \<subseteq> set cs1" using no_right_mrg_plan[OF s1 s2] by simp
      show ?thesis using esemi_join[OF f1 f2 sub t1 t2, of pos]
          etabc_join_sub_res[OF f1 f2 sub] ne ne2 True
        by (simp add: mk_djoin_def)
    next
      case nr: False
      then have nsub: "\<not> set cs2 \<subseteq> set cs1" using no_right_mrg_plan[OF s1 s2] by simp
      then have p: "pos" using neg by blast
      show ?thesis
      proof (cases "no_left ?p")
        case True
        then have sub: "set cs1 \<subseteq> set cs2" using no_left_mrg_plan[OF s1 s2] by simp
        show ?thesis using esup_join[OF f1 f2 sub t1 t2]
            merge_cols_sub_right[OF s1 s2 sub] ne ne2 nr True p
          by (simp add: mk_djoin_def)
      next
        case False
        show ?thesis using etabc_gen_join[OF f1 f2 t1 t2 fT fT'] ne ne2 nr False p
          by (simp add: mk_djoin_def Let_def)
      qed
    qed
  qed
qed

theorem gbin_join_join:
  assumes f1: "eframe ks1 cs1" and f2: "eframe ks2 cs2"
    and t1: "table ks1 (T :: event_data table)" and t2: "table ks2 T'"
    and neg: "\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1"
    and fT: "finite T" and fT': "finite T'"
  shows "gbin_join (mk_djoin cs1 cs2) (etabc ks1 cs1 T) pos (etabc ks2 cs2 T')
       = etabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T pos ks2 T')"
proof (cases "T = {}")
  case True
  then show ?thesis
    by (cases pos) (simp_all add: gbin_join_def etabc_empty_iff join_False_code empty_table_def)
next
  case T: False
  show ?thesis
  proof (cases "T' = {}")
    case True
    show ?thesis
    proof (cases pos)
      case False
      then have sub: "set cs2 \<subseteq> set cs1" by (rule neg)
      show ?thesis using T True False etabc_join_sub_res[OF f1 f2 sub]
        by (simp add: gbin_join_def etabc_empty_iff join_False_code empty_table_def)
    qed (use T True in \<open>simp add: gbin_join_def etabc_empty_iff empty_table_def\<close>)
  next
    case False
    then show ?thesis using T
      by (simp add: gbin_join_def etabc_empty_iff gbin_join0_join[OF f1 f2 t1 t2 neg fT fT'])
  qed
qed

subsection \<open>Multi-way join as a fold\<close>

lemma set_kands_cols: "set (kands_cols acc kss) = set acc \<union> (\<Union>k \<in> set kss. set k)"
  by (induct kss arbitrary: acc) auto

lemma distinct_kands_cols:
  "distinct acc \<Longrightarrow> \<forall>k \<in> set kss. distinct k \<Longrightarrow> distinct (kands_cols acc kss)"
  by (induct kss arbitrary: acc) auto

lemma eframe_eands_cols:
  assumes "list_all2 eframe kss css" and "eframe acc c"
  shows "eframe (kands_cols acc kss) (eands_cols c css)"
  using assms
proof (induct kss css arbitrary: acc c rule: list_all2_induct)
  case (Cons k ks c' cs)
  show ?case using Cons(3)[OF eframe_merge[OF Cons(4) Cons(1)]] by simp
qed simp

lemma kands_pos_iff:
  assumes "distinct acc" "table acc t" "\<forall>(k, u) \<in> set us. distinct k \<and> table k u"
  shows "z \<in> kands_pos acc t us \<longleftrightarrow> wf_tuple (kands_cols acc (map fst us)) z \<and>
    restrict acc (kands_cols acc (map fst us)) z \<in> t \<and>
    (\<forall>(k, u) \<in> set us. restrict k (kands_cols acc (map fst us)) z \<in> u)"
  using assms
proof (induct us arbitrary: acc t)
  case (Cons ku us)
  obtain k u where ku: "ku = (k, u)" by (cases ku)
  let ?U = "cols_union acc k" and ?K = "kands_cols (cols_union acc k) (map fst us)"
  have ek: "distinct k" "table k u" using Cons(4) ku by auto
  have tj: "table ?U (join acc t True k u)"
    using Cons(3) ek by (intro join_table) auto
  have sub: "set ?U \<subseteq> set ?K" by (simp add: set_kands_cols)
  have IH: "z \<in> kands_pos ?U (join acc t True k u) us \<longleftrightarrow> wf_tuple ?K z \<and>
      restrict ?U ?K z \<in> join acc t True k u \<and> (\<forall>(k, u) \<in> set us. restrict k ?K z \<in> u)"
    using Cons(1)[of ?U "join acc t True k u"] Cons(2,4) ek tj by auto
  have j: "restrict ?U ?K z \<in> join acc t True k u \<longleftrightarrow>
      restrict acc ?K z \<in> t \<and> restrict k ?K z \<in> u"
    using join_restrict[OF Cons(2) ek(1) Cons(3) ek(2), of True "restrict ?U ?K z"]
    by (simp add: restrict_restrict sub)
  show ?case using IH j by (auto simp: ku)
qed (auto simp: restrict_idle dest: tableD)

lemma kands_neg_iff:
  assumes "distinct acc" "table acc t" "\<forall>(k, u) \<in> set us. distinct k \<and> table k u \<and> set k \<subseteq> set acc"
  shows "z \<in> kands_neg acc t us \<longleftrightarrow> z \<in> t \<and> (\<forall>(k, u) \<in> set us. restrict k acc z \<notin> u)"
  using assms
proof (induct us arbitrary: t)
  case (Cons ku us)
  obtain k u where ku: "ku = (k, u)" by (cases ku)
  have ek: "distinct k" "table k u" "set k \<subseteq> set acc" using Cons(4) ku by auto
  have j: "join acc t False k u = {a \<in> t. restrict k acc a \<notin> u}"
    using join_sub_eq[OF Cons(2) ek(1) Cons(3) ek(2,3), of False] by simp
  have tj: "table acc (join acc t False k u)"
    using Cons(3) by (auto simp: j table_def)
  show ?case using Cons(1)[OF Cons(2) tj] Cons(4) by (auto simp: ku j)
qed simp

theorem gands_pos_dtabc:
  assumes "eframe acc c" and "table acc T" and "finite T"
    and "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Us"
  shows "gands_pos (eands_plans c (map snd kcs)) (etabc acc c T) (map2 (\<lambda>(k, c). etabc k c) kcs Us)
       = etabc (kands_cols acc (map fst kcs)) (eands_cols c (map snd kcs)) (kands_pos acc T (zip (map fst kcs) Us))"
  using assms
proof (induct kcs arbitrary: acc c T Us)
  case (Cons kc kcs)
  obtain k c' where kc: "kc = (k, c')" by (cases kc)
  from Cons(5) obtain U Us' where U: "Us = U # Us'" and wf: "wf_operand k c' U"
    and rest: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Us'"
    by (cases Us) (auto simp: kc)
  have f': "eframe k c'" and tU: "table k U" and fU: "finite U" using wf by (auto simp: wf_operand_def)
  have j: "gbin_join (mk_djoin c c') (etabc acc c T) True (etabc k c' U)
      = etabc (cols_union acc k) (merge_cols c c') (join acc T True k U)"
    by (rule gbin_join_join[OF Cons(2) f' Cons(3) tU _ Cons(4) fU]) simp
  have t: "table (cols_union acc k) (join acc T True k U)"
    using Cons(3) tU by (intro join_table) auto
  show ?case
    unfolding U kc using Cons(1)[OF eframe_merge[OF Cons(2) f'] t finite_join[OF Cons(4) fU] rest]
    by (simp add: j)
qed simp

theorem gands_neg_dtabc:
  assumes "eframe acc c" and "table acc T" and "finite T"
    and "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Vs" and "\<forall>c' \<in> set (map snd kcs). set c' \<subseteq> set c"
  shows "gands_neg (eands_plans c (map snd kcs)) (etabc acc c T) (map2 (\<lambda>(k, c). etabc k c) kcs Vs)
       = etabc acc c (kands_neg acc T (zip (map fst kcs) Vs))"
  using assms
proof (induct kcs arbitrary: T Vs)
  case (Cons kc kcs)
  obtain k c' where kc: "kc = (k, c')" by (cases kc)
  from Cons(5) obtain V Vs' where V: "Vs = V # Vs'" and wf: "wf_operand k c' V"
    and rest: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Vs'"
    by (cases Vs) (auto simp: kc)
  have f': "eframe k c'" and tV: "table k V" and fV: "finite V" using wf by (auto simp: wf_operand_def)
  have sub: "set c' \<subseteq> set c" using Cons(6) kc by simp
  note res = etabc_join_sub_res[OF Cons(2) f' sub]
  have j: "gbin_join (mk_djoin c c') (etabc acc c T) False (etabc k c' V)
      = etabc acc c (join acc T False k V)"
    using gbin_join_join[OF Cons(2) f' Cons(3) tV _ Cons(4) fV, of False] sub res by simp
  have t: "table acc (join acc T False k V)"
    using Cons(3) tV sub Cons(2) f' by (intro join_table) (auto simp: eframe_def res)
  show ?case
    unfolding V kc
    using Cons(1)[OF Cons(2) t finite_join[OF Cons(4) fV] rest] Cons(6) res
    by (simp add: j)
qed simp

lemma mmulti_join_kands:
  assumes acc: "distinct acc" "table acc T"
    and pos: "\<forall>(k, u) \<in> set (zip kss Us). distinct k \<and> table k u" "length kss = length Us"
    and neg: "\<forall>(k, u) \<in> set (zip nks Vs). distinct k \<and> table k u \<and> set k \<subseteq> set (kands_cols acc kss)"
      "length nks = length Vs"
    and cs: "distinct cs" "set cs = set (kands_cols acc kss)"
  shows "mmulti_join cs (acc # kss) nks ((T # Us) @ Vs)
       = restrict cs (kands_cols acc kss) ` kands_neg (kands_cols acc kss) (kands_pos acc T (zip kss Us)) (zip nks Vs)"
proof -
  let ?K = "kands_cols acc kss"
  have dks: "distinct k" if k: "k \<in> set kss" for k
  proof -
    obtain u where "(k, u) \<in> set (zip kss Us)"
      using in_set_impl_in_set_zip1[OF pos(2) k] by blast
    then show ?thesis using pos(1) by auto
  qed
  have dK: "distinct ?K" using acc(1) dks by (intro distinct_kands_cols) auto
  have tP: "table ?K (kands_pos acc T (zip kss Us))"
    using kands_pos_iff[OF acc pos(1)] pos(2) by (auto simp: table_def)
  have la: "list_all2 (\<lambda>A X. distinct A \<and> table A X) ((acc # kss) @ nks) ((T # Us) @ Vs)"
    using acc pos neg by (auto simp: list_all2_append list_all2_iff)
  have nsub: "(\<Union>A\<in>set nks. set A) \<subseteq> (\<Union>A\<in>set (acc # kss). set A)"
  proof
    fix x assume "x \<in> (\<Union>A\<in>set nks. set A)"
    then obtain A where "A \<in> set nks" "x \<in> set A" by auto
    then obtain V where "(A, V) \<in> set (zip nks Vs)" using neg(2)
      by (metis in_set_impl_in_set_zip1)
    then show "x \<in> (\<Union>A\<in>set (acc # kss). set A)" using neg(1) \<open>x \<in> set A\<close>
      by (force simp: set_kands_cols)
  qed
  have setK: "set cs = (\<Union>A\<in>set (acc # kss). set A)" using cs(2) by (simp add: set_kands_cols)
  have mj: "z \<in> mmulti_join cs (acc # kss) nks ((T # Us) @ Vs) \<longleftrightarrow> wf_tuple cs z \<and>
      restrict acc cs z \<in> T \<and> (\<forall>(k, u) \<in> set (zip kss Us). restrict k cs z \<in> u) \<and>
      (\<forall>(k, v) \<in> set (zip nks Vs). restrict k cs z \<notin> v)" for z
    using mmulti_join_correct[OF _ la nsub cs(1) setK, of z] pos(2) neg(2)
    by (simp add: list_all2_iff)
  have rr: "restrict ?K cs (restrict cs ?K y) = y" if "wf_tuple ?K y" for y
    using that cs dK by (simp add: restrict_restrict restrict_idle)
  have rr': "restrict cs ?K (restrict ?K cs z) = z" if "wf_tuple cs z" for z
    using that cs by (simp add: restrict_restrict restrict_idle)
  have sk: "set k \<subseteq> set ?K \<Longrightarrow> restrict k ?K (restrict ?K cs z) = restrict k cs z" for k z
    using cs(2) by (simp add: restrict_restrict)
  have ka: "set acc \<subseteq> set ?K" by (simp add: set_kands_cols)
  have kp: "(k, u) \<in> set (zip kss Us) \<Longrightarrow> set k \<subseteq> set ?K" for k u
    by (auto simp: set_kands_cols dest: set_zip_leftD)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix z assume z: "z \<in> mmulti_join cs (acc # kss) nks ((T # Us) @ Vs)"
    then have m: "wf_tuple cs z" "restrict acc cs z \<in> T" "\<forall>(k, u) \<in> set (zip kss Us). restrict k cs z \<in> u"
      "\<forall>(k, v) \<in> set (zip nks Vs). restrict k cs z \<notin> v" using mj by auto
    let ?y = "restrict ?K cs z"
    have "restrict k ?K ?y \<in> u" if "(k, u) \<in> set (zip kss Us)" for k u
      using m(3) that by (auto simp: sk[OF kp[OF that]])
    then have "?y \<in> kands_pos acc T (zip kss Us)"
      unfolding kands_pos_iff[OF acc pos(1)] using m(2) pos(2) by (auto simp: sk[OF ka])
    moreover have "restrict k ?K ?y \<notin> v" if "(k, v) \<in> set (zip nks Vs)" for k v
    proof -
      have "set k \<subseteq> set ?K" using neg(1) that by auto
      then show ?thesis using m(4) that by (auto simp: sk)
    qed
    ultimately have "?y \<in> kands_neg ?K (kands_pos acc T (zip kss Us)) (zip nks Vs)"
      unfolding kands_neg_iff[OF dK tP neg(1)] by auto
    then show "z \<in> restrict cs ?K ` kands_neg ?K (kands_pos acc T (zip kss Us)) (zip nks Vs)"
      using rr'[OF m(1)] by (auto intro!: image_eqI[where x = ?y])
  next
    fix z assume "z \<in> restrict cs ?K ` kands_neg ?K (kands_pos acc T (zip kss Us)) (zip nks Vs)"
    then obtain y where y: "y \<in> kands_neg ?K (kands_pos acc T (zip kss Us)) (zip nks Vs)"
      and z: "z = restrict cs ?K y" by auto
    then have yp: "y \<in> kands_pos acc T (zip kss Us)" and yn: "\<forall>(k, v) \<in> set (zip nks Vs). restrict k ?K y \<notin> v"
      using kands_neg_iff[OF dK tP neg(1)] by auto
    then have wy: "wf_tuple ?K y" "restrict acc ?K y \<in> T" "\<forall>(k, u) \<in> set (zip kss Us). restrict k ?K y \<in> u"
      using kands_pos_iff[OF acc pos(1)] pos(2) by auto
    have yz: "y = restrict ?K cs z" using rr[OF wy(1)] z by simp
    have zk: "restrict k cs z = restrict k ?K y" if "set k \<subseteq> set ?K" for k
      using sk[OF that, of z] by (simp add: yz)
    have "restrict k cs z \<in> u" if "(k, u) \<in> set (zip kss Us)" for k u
      using wy(3) that by (auto simp: zk[OF kp[OF that]])
    moreover have "restrict k cs z \<notin> v" if "(k, v) \<in> set (zip nks Vs)" for k v
    proof -
      have "set k \<subseteq> set ?K" using neg(1) that by auto
      then show ?thesis using yn that by (auto simp: zk)
    qed
    ultimately show "z \<in> mmulti_join cs (acc # kss) nks ((T # Us) @ Vs)"
      unfolding mj using wy(2) by (auto simp: zk[OF ka] simp del: mmulti_join.simps) (simp add: z)
  qed
qed

subsection \<open>Terms, matches and the existential\<close>

lemma col_pos_length: "c \<in> set cs \<Longrightarrow> col_pos cs c < length cs"
  by (induct cs) auto

lemma fv_reindex_trm:
  "Formula.fv_trm t \<subseteq> set cs \<Longrightarrow> Formula.fv_trm (reindex_trm cs t) \<subseteq> {0..<length cs}"
  by (induct t) (auto simp: col_pos_length)

lemma set_cols:
  assumes "finite A"
  shows "sorted_wrt (<) (set_cols A)" "set (set_cols A) = A"
  using assms unfolding set_cols_def
  by (subst csorted_list_of_set_split;
      auto simp: ccompare_nat_def ID_Some ord_defs strict_sorted_iff)+

lemma set_cols_eqI:
  assumes f: "finite A" and s: "sorted_wrt (<) xs" and e: "set xs = A"
  shows "xs = set_cols A"
  by (rule strict_sorted_equal) (use s e set_cols[OF f] in auto)

lemma set_cols_empty: "set_cols {} = []"
  by (rule set_cols_eqI[symmetric]) simp_all

lemma set_cols_upt: "set_cols {0..<m} = [0..<m]"
  by (rule set_cols_eqI[symmetric]) (simp_all add: strict_sorted_iff)

lemma eframe_set_cols: "distinct ks \<Longrightarrow> eframe ks (set_cols (set ks))"
  by (simp add: eframe_def set_cols)

lemma umatch_match: "umatch tms xs = match tms xs"
  by (induct tms xs rule: umatch.induct) auto

lemma these_map_option_image: "Option.these (map_option g ` S) = g ` Option.these S"
  by (force simp: Option.these_def image_iff)

theorem umatch_table_etabc:
  assumes "set cs \<subseteq> set ks"
  shows "umatch_table tms cs X = etabc ks cs (tabulate_match ks ` Option.these (match tms ` X))"
proof -
  have "umatch_table tms cs X = Option.these (map_option (\<lambda>f. map (\<lambda>c. the (f c)) cs) ` match tms ` X)"
    by (simp add: umatch_table_def umatch_match image_image)
  also have "\<dots> = (\<lambda>f. map (\<lambda>c. the (f c)) cs) ` Option.these (match tms ` X)"
    by (rule these_map_option_image)
  also have "\<dots> = etabc ks cs (tabulate_match ks ` Option.these (match tms ` X))"
    unfolding etabc_def image_image restrict_map tabulate_match_def
    using assms by (intro image_cong[OF refl] map_cong[OF refl]) (auto simp: tup_get_map_self)
  finally show ?thesis .
qed

lemma fold_pred_cols_simple:
  "is_simple_pattern tms m \<Longrightarrow> \<forall>c \<in> set acc. c < m \<Longrightarrow>
     fold (\<lambda>t cs. cols_union cs (Formula.fv_trm_list t)) tms acc = acc @ smp_cols tms"
proof (induct tms m arbitrary: acc rule: is_simple_pattern.induct)
  case (2 y ts x)
  have "y \<notin> set acc" using 2(2,3) by auto
  then have "cols_union acc [y] = acc @ [y]" by (simp add: cols_union_def)
  moreover have "\<forall>c \<in> set (acc @ [y]). c < Suc y" using 2(2,3) by auto
  ultimately show ?case using 2(1)[of "acc @ [y]"] 2(2) by simp
qed simp_all

lemma pred_cols_simple: "is_simple_pattern tms 0 \<Longrightarrow> pred_cols tms = smp_cols tms"
  using fold_pred_cols_simple[of tms 0 "[]"] by (simp add: pred_cols_def)

lemma ex_drop0_pos: "sorted_wrt (<) ccs \<Longrightarrow> \<forall>c \<in> set (if ex_drop0 ccs then tl ccs else ccs). 0 < c"
  by (cases ccs) (auto simp: ex_drop0_def)

theorem etabc_exists:
  assumes f: "eframe ks ccs"
  shows "(if ex_drop0 ccs then tl ` etabc ks ccs T else etabc ks ccs T)
       = etabc (ex_cols ks) (eex_cols ccs) (ex_proj ks ` T)"
proof -
  let ?c = "if ex_drop0 ccs then tl ccs else ccs"
  have s: "sorted_wrt (<) ccs" using eframeD(2)[OF f] .
  have l: "(if ex_drop0 ccs then tl ` etabc ks ccs T else etabc ks ccs T)
      = (\<lambda>x. map (tup_get ks x) ?c) ` T"
    by (auto simp: etabc_def restrict_map map_tl)
  have cc: "c \<in> set ccs" if "c \<in> set ?c" for c
    using that by (cases ccs) (auto split: if_splits)
  have mem: "c \<in> set ks" "c \<noteq> 0" if "c \<in> set ?c" for c
    using cc[OF that] that ex_drop0_pos[OF s] eframeD(3)[OF f] by auto
  have e: "tup_get (ex_cols ks) (ex_proj ks x) (c - Suc 0) = tup_get ks x c" if "c \<in> set ?c" for x c
    using tup_get_ex_proj[of c ks x] mem[OF that] by simp
  show ?thesis
    unfolding l unfolding etabc_def restrict_map eex_cols_def image_image
  proof (intro image_cong[OF refl])
    fix x
    show "map (tup_get ks x) ?c = map (tup_get (ex_cols ks) (ex_proj ks x)) (map (\<lambda>c. c - Suc 0) ?c)"
      unfolding map_map o_def by (rule map_cong[OF refl]) (rule e[symmetric])
  qed
qed

subsection \<open>Auxiliary lists of Since and Until\<close>

theorem etabc_join_sub:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and tR: "table kR T" and tL: "table kL U"
  shows "etabc kR cR (join kR T pos kL U) = join cR (etabc kR cR T) pos cL (etabc kL cL U)"
proof -
  have sub': "set cL \<subseteq> set cR" using sub eframeD(3)[OF fR] eframeD(3)[OF fL] by simp
  have tR': "table cR (etabc kR cR T)" and tL': "table cL (etabc kL cL U)"
    by (simp_all add: table_etabc)
  have key: "restrict cL cR (restrict cR kR a) = restrict cL kL (restrict kL kR a)" for a :: "'a list"
    using sub sub' eframeD(3)[OF fR] eframeD(3)[OF fL] by (simp add: restrict_restrict)
  have mem: "(restrict cL kL (restrict kL kR a) \<in> etabc kL cL U) = (restrict kL kR a \<in> U)" for a :: "'a list"
    by (rule etabc_in_iff[OF fL tL]) simp
  show ?thesis
    unfolding join_sub_eq[OF eframeD(1)[OF fR] eframeD(1)[OF fL] tR tL sub]
      join_sub_eq[OF eframeD(4)[OF fR] eframeD(4)[OF fL] tR' tL' sub']
  proof (intro equalityI subsetI)
    fix d assume "d \<in> etabc kR cR {a \<in> T. (restrict kL kR a \<in> U) = pos}"
    then obtain a where a: "a \<in> T" "(restrict kL kR a \<in> U) = pos" "d = restrict cR kR a"
      by (auto simp: etabc_def)
    have "d \<in> etabc kR cR T" using a(1,3) by (auto simp: etabc_def)
    then show "d \<in> {d \<in> etabc kR cR T. (restrict cL cR d \<in> etabc kL cL U) = pos}"
      using a(2,3) by (simp add: key mem)
  next
    fix d assume d: "d \<in> {d \<in> etabc kR cR T. (restrict cL cR d \<in> etabc kL cL U) = pos}"
    then obtain a where a: "a \<in> T" "d = restrict cR kR a" by (auto simp: etabc_def)
    then have "(restrict kL kR a \<in> U) = pos" using d by (simp add: key mem)
    then show "d \<in> etabc kR cR {a \<in> T. (restrict kL kR a \<in> U) = pos}"
      using a unfolding etabc_def by blast
  qed
qed

lemma table_join_sub: "table kR X \<Longrightarrow> table kL Y \<Longrightarrow> set kL \<subseteq> set kR \<Longrightarrow> table kR (join kR X b kL Y)"
  by (rule join_table[of kR X kL Y b kR]) (auto simp: cols_union_def filter_empty_conv)

lemma eauxlist_filter:
  "eauxlist ks cs (filter (\<lambda>(t, rel). P t) aux) = filter (\<lambda>(t, rel). P t) (eauxlist ks cs aux)"
  by (induct aux) (auto simp: eauxlist_def)

lemma eauxlist_join:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and wf: "\<forall>(t, rel) \<in> set aux. table kR rel" and t1: "table kL rel1"
  shows "eauxlist kR cR (map (\<lambda>(t, rel). (t, join kR rel pos kL rel1)) aux)
       = map (\<lambda>(t, rel). (t, join cR rel pos cL (etabc kL cL rel1))) (eauxlist kR cR aux)"
  using wf by (induct aux) (auto simp: eauxlist_def etabc_join_sub[OF fR fL sub _ t1])

lemma eauxlist_add_new_table:
  "eauxlist ks cs (case aux of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # aux)
   = (case eauxlist ks cs aux of [] \<Rightarrow> [(cur, etabc ks cs rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> etabc ks cs rel2) # r
                         else (cur, etabc ks cs rel2) # eauxlist ks cs aux)"
  by (cases aux) (auto simp: eauxlist_def etabc_Un_img)

lemma etabc_result:
  "etabc ks cs (foldr (\<union>) [rel. (t, rel) \<leftarrow> aux, P t] {})
     = foldr (\<union>) [rel. (t, rel) \<leftarrow> eauxlist ks cs aux, P t] {}"
  by (induct aux) (auto simp: eauxlist_def etabc_Un_img)

lemma eauxlist_wf_join:
  assumes "\<forall>(t, rel) \<in> set aux. table kR rel" and "set kL \<subseteq> set kR" and "table kL rel1"
  shows "\<forall>(t, rel) \<in> set (map (\<lambda>(t, rel). (t, join kR rel pos kL rel1)) aux). table kR rel"
  using assms by (auto intro: table_join_sub)

lemma eauxlist_wf_add_new_table:
  assumes "\<forall>(t, rel) \<in> set aux. table ks rel" and "table ks rel2"
  shows "\<forall>(t, rel) \<in> set (case aux of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # aux). table ks rel"
  using assms by (cases aux) (auto simp: table_def)

lemma eauxlist3_update_until:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and wf: "\<forall>(t, a1, a2) \<in> set aux. table kL a1 \<and> table kR a2"
    and t1: "table kL rel1" and t2: "table kR rel2"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and aL': "args_L args' = cL" and aR': "args_R args' = cR"
    and iv: "args_ivl args' = args_ivl args" and po: "args_pos args' = args_pos args"
  shows "eauxlist3 kL cL kR cR (update_until args rel1 rel2 nt aux)
       = update_until args' (etabc kL cL rel1) (etabc kR cR rel2) nt (eauxlist3 kL cL kR cR aux)"
  using wf
  by (induct aux)
    (auto simp: eauxlist3_def update_until_def iv po aL aR aL' aR' empty_table_def etabc_Un_img
       etabc_Int[OF fL _ t1] etabc_join_sub[OF fR fL sub t2])

lemma eauxlist3_eval_until:
  "eval_until I nt aux = (res, aux') \<Longrightarrow>
     eval_until I nt (eauxlist3 kL cL kR cR aux) = (map (etabc kR cR) res, eauxlist3 kL cL kR cR aux')"
  by (induct I nt aux arbitrary: res aux' rule: eval_until.induct)
    (auto simp: eauxlist3_def split: if_splits prod.splits)

lemma table_Int: "table ks X \<Longrightarrow> table ks (X \<inter> Y)"
  by (auto simp: table_def)

lemma table_Diff: "table ks X \<Longrightarrow> table ks (X - Y)"
  by (auto simp: table_def)

lemma eauxlist3_wf_update_until:
  assumes wf: "\<forall>(t, a1, a2) \<in> set aux. table kL a1 \<and> table kR a2"
    and sub: "set kL \<subseteq> set kR" and t1: "table kL rel1" and t2: "table kR rel2"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
  shows "\<forall>(t, a1, a2) \<in> set (update_until args rel1 rel2 nt aux). table kL a1 \<and> table kR a2"
proof safe
  have w: "\<And>t b1 b2. (t, b1, b2) \<in> set aux \<Longrightarrow> table kL b1 \<and> table kR b2"
    using wf by auto
  fix t a1 a2 assume m: "(t, a1, a2) \<in> set (update_until args rel1 rel2 nt aux)"
  show "table kL a1"
    using m t1 by (auto simp: update_until_def dest!: w intro: table_Int table_Un)
  show "table kR a2"
    using m t1 t2 sub
    by (auto simp: update_until_def aL aR dest!: w intro!: table_Un intro: table_join_sub)
qed

subsection \<open>Buffers of reordered tables\<close>

text \<open>A buffer never looks inside a tuple, so a buffer of reordered tables behaves as the
  reordering of the kernel's buffer.\<close>

subsubsection \<open>Two-operand buffers\<close>

lemma mbuf2_take_map:
  "(\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set ys \<Longrightarrow> g (h a) (k b) = m (f a b)) \<Longrightarrow>
   mbuf2_take f (xs, ys) = (zs, (xs', ys')) \<Longrightarrow>
   mbuf2_take g (map h xs, map k ys) = (map m zs, (map h xs', map k ys'))"
proof (induct xs arbitrary: ys zs xs' ys')
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  note IH = Cons(1) and P1 = Cons(2) and P2 = Cons(3)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using P2 by simp
  next
    case (Cons y ys2)
    note e = Cons
    obtain ws as bs where w: "mbuf2_take f (xs, ys2) = (ws, (as, bs))"
      by (cases "mbuf2_take f (xs, ys2)") auto
    have p1: "\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set ys2 \<Longrightarrow> g (h a) (k b) = m (f a b)"
      using P1 e by simp
    have ih: "mbuf2_take g (map h xs, map k ys2) = (map m ws, (map h as, map k bs))"
      by (rule IH[OF p1 w])
    have d: "zs = f x y # ws" "xs' = as" "ys' = bs" using P2 e w by auto
    show ?thesis using P1 e w ih d by simp
  qed
qed

lemma mprev_next_map:
  "h empty_table = empty_table \<Longrightarrow> mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
     mprev_next I (map h xs) ts = (map h ys, map h xs', ts')"
  by (induct I xs ts arbitrary: ys xs' ts' rule: mprev_next.induct)
    (auto split: prod.splits)

text \<open>The verified Until structure accepts only timestamps no smaller than its current one, so
  the relation is indexed by that timestamp.\<close>

lemma mbuf2t_take_rel_ts:
  "(\<And>a b t u za z'a. a \<in> set xs \<Longrightarrow> b \<in> set ys \<Longrightarrow> R u za z'a \<Longrightarrow> u \<le> t \<Longrightarrow>
      R t (f a b t za) (g (h a) (k b) t z'a)) \<Longrightarrow>
   R u0 z z' \<Longrightarrow> u0 \<le> t0 \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. u0 \<le> t) \<Longrightarrow>
   mbuf2t_take f z (xs, ys) t0 ts = (w, (xs', ys'), nt, ts') \<Longrightarrow>
   mbuf2t_take g z' (map h xs, map k ys) t0 ts = (w2, buf2, nt2, ts2) \<Longrightarrow>
   (\<exists>u. R u w w2 \<and> u \<le> nt \<and> (\<forall>t \<in> set ts'. u \<le> t)) \<and> sorted ts' \<and>
     (nt = t0 \<or> nt \<in> set ts) \<and> set ts' \<subseteq> set ts \<and>
     buf2 = (map h xs', map k ys') \<and> nt2 = nt \<and> ts2 = ts'"
proof (induct xs arbitrary: ys z z' u0 t0 ts w xs' ys' nt ts' w2 buf2 nt2 ts2)
  case Nil
  then show ?case by (cases ts) (auto intro!: exI[of _ u0])
next
  case (Cons x xs)
  note IH = Cons(1) and P1 = Cons(2) and P2 = Cons(3) and P3 = Cons(4)
    and P4 = Cons(5) and P5 = Cons(6) and P6 = Cons(7) and P7 = Cons(8)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using P2 P3 P4 P5 P6 P7 by (cases ts) (auto intro!: exI[of _ u0])
  next
    case (Cons y ys2)
    note ysC = Cons
    show ?thesis
    proof (cases ts)
      case Nil
      then show ?thesis using P2 P3 P6 P7 ysC by (auto intro!: exI[of _ u0])
    next
      case (Cons t ts3)
      note tsC = Cons
      have ut: "u0 \<le> t" using P5 tsC by simp
      have r: "R t (f x y t z) (g (h x) (k y) t z')"
        using P1[of x y u0 z z' t] P2 ut ysC by simp
      have p1: "\<And>a b t' u za z'a. a \<in> set xs \<Longrightarrow> b \<in> set ys2 \<Longrightarrow> R u za z'a \<Longrightarrow> u \<le> t' \<Longrightarrow>
          R t' (f a b t' za) (g (h a) (k b) t' z'a)" using P1 ysC by simp
      have s1: "mbuf2t_take f (f x y t z) (xs, ys2) t ts3 = (w, (xs', ys'), nt, ts')"
        using P6 ysC tsC by simp
      have s2: "mbuf2t_take g (g (h x) (k y) t z') (map h xs, map k ys2) t ts3
          = (w2, buf2, nt2, ts2)"
        using P7 ysC tsC by simp
      have "(\<exists>u. R u w w2 \<and> u \<le> nt \<and> (\<forall>t' \<in> set ts'. u \<le> t')) \<and> sorted ts' \<and>
          (nt = t \<or> nt \<in> set ts3) \<and> set ts' \<subseteq> set ts3 \<and>
          buf2 = (map h xs', map k ys') \<and> nt2 = nt \<and> ts2 = ts'"
        by (rule IH[OF p1 r order_refl _ _ s1 s2]) (use P4 tsC in auto)
      then show ?thesis using tsC by auto
    qed
  qed
qed

lemma mbuf2t_take_rel:
  "(\<And>a b t za z'a. a \<in> set xs \<Longrightarrow> b \<in> set ys \<Longrightarrow> R za z'a \<Longrightarrow>
      R (f a b t za) (g (h a) (k b) t z'a)) \<Longrightarrow>
   R z z' \<Longrightarrow>
   mbuf2t_take f z (xs, ys) t0 ts = (w, (xs', ys'), nt, ts') \<Longrightarrow>
   mbuf2t_take g z' (map h xs, map k ys) t0 ts = (w2, buf2, nt2, ts2) \<Longrightarrow>
   R w w2 \<and> buf2 = (map h xs', map k ys') \<and> nt2 = nt \<and> ts2 = ts'"
proof (induct xs arbitrary: ys z z' t0 ts w xs' ys' nt ts' w2 buf2 nt2 ts2)
  case Nil
  then show ?case by (cases ts) auto
next
  case (Cons x xs)
  note IH = Cons.hyps and P = Cons.prems
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using P(2-4) by (cases ts) auto
  next
    case (Cons y ys2)
    note ysC = Cons
    show ?thesis
    proof (cases ts)
      case Nil
      then show ?thesis using P(2-4) ysC by auto
    next
      case (Cons t ts3)
      note tsC = Cons
      have r: "R (f x y t z) (g (h x) (k y) t z')"
        using P(1)[of x y z z' t] P(2) ysC by simp
      show ?thesis
        by (rule IH[OF _ r, of ys2 t ts3]) (use P ysC tsC in auto)
    qed
  qed
qed

lemma mbuf2t_take_sub:
  "mbuf2t_take f z (xs, ys) t0 ts = (w, (xs', ys'), nt, ts') \<Longrightarrow>
     set xs' \<subseteq> set xs \<and> set ys' \<subseteq> set ys"
proof (induct xs arbitrary: ys z t0 ts w xs' ys' nt ts')
  case Nil
  then show ?case by (auto split: list.splits)
next
  case (Cons x xs)
  note IH = Cons(1) and P = Cons(2)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using P by (auto split: list.splits)
  next
    case (Cons y ys0)
    note ysC = Cons
    show ?thesis
    proof (cases ts)
      case Nil
      then show ?thesis using P ysC by simp
    next
      case (Cons t ts0)
      have "mbuf2t_take f (f x y t z) (xs, ys0) t ts0 = (w, (xs', ys'), nt, ts')"
        using P ysC Cons by simp
      from IH[OF this] show ?thesis using ysC by auto
    qed
  qed
qed

subsubsection \<open>Multi-way buffer\<close>

text \<open>Each slot has its own column list, so the reordering is a list of maps applied slotwise;
  tables come from fixed sets @{term Ss}, as the multi-way join needs well-formed operands.\<close>

lemma map2_map_empty_iff:
  "length hs = length buf \<Longrightarrow> ([] \<in> set (map2 map hs buf)) = ([] \<in> set buf)"
  by (induct hs buf rule: list_induct2) auto

lemma map2_map_nil_iff: "length hs = length buf \<Longrightarrow> (map2 map hs buf = []) = (buf = [])"
  by (induct hs buf rule: list_induct2) auto

lemma map2_map_hd:
  "length hs = length buf \<Longrightarrow> [] \<notin> set buf \<Longrightarrow>
     map hd (map2 map hs buf) = map2 (\<lambda>h a. h a) hs (map hd buf)"
  by (induct hs buf rule: list_induct2) (auto simp: hd_map)

lemma map2_map_tl:
  "length hs = length buf \<Longrightarrow> [] \<notin> set buf \<Longrightarrow>
     map tl (map2 map hs buf) = map2 map hs (map tl buf)"
  by (induct hs buf rule: list_induct2) (auto simp: map_tl)

lemma mbufn_take_rel:
  "length hs = length buf \<Longrightarrow> length Ss = length buf \<Longrightarrow>
   (\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i) \<Longrightarrow>
   (\<And>as u u'. length as = length hs \<Longrightarrow> (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> R u u' \<Longrightarrow>
      R (f as u) (g (map2 (\<lambda>h a. h a) hs as) u')) \<Longrightarrow>
   R z z' \<Longrightarrow>
   mbufn_take f z buf = (w, buf') \<Longrightarrow>
   mbufn_take g z' (map2 map hs buf) = (w2, buf2) \<Longrightarrow>
   R w w2 \<and> buf2 = map2 map hs buf'"
proof (induct f z buf arbitrary: z' w buf' w2 buf2 rule: mbufn_take.induct)
  case (1 f z buf)
  note IH = 1(1) and L1 = 1(2) and L2 = 1(3) and SUB = 1(4)
    and STEP = 1(5) and RZ = 1(6) and E1 = 1(7) and E2 = 1(8)
  show ?case
  proof (cases "buf = [] \<or> [] \<in> set buf")
    case True
    then have "map2 map hs buf = [] \<or> [] \<in> set (map2 map hs buf)"
      by (simp only: map2_map_nil_iff[OF L1] map2_map_empty_iff[OF L1])
    then show ?thesis using True RZ E1 E2 by simp
  next
    case False
    then have ne: "\<not> (map2 map hs buf = [] \<or> [] \<in> set (map2 map hs buf))"
      by (simp only: map2_map_nil_iff[OF L1] map2_map_empty_iff[OF L1]) simp
    have las: "length (map hd buf) = length hs" using L1 by simp
    have mem: "\<forall>i < length (map hd buf). map hd buf ! i \<in> Ss ! i"
    proof (intro allI impI)
      fix i assume i: "i < length (map hd buf)"
      then have i': "i < length buf" by simp
      then have "buf ! i \<noteq> []" using False by (auto simp: in_set_conv_nth)
      then have "hd (buf ! i) \<in> set (buf ! i)" by simp
      then show "map hd buf ! i \<in> Ss ! i" using SUB i' by auto
    qed
    have r: "R (f (map hd buf) z) (g (map2 (\<lambda>h a. h a) hs (map hd buf)) z')"
      by (rule STEP[OF las mem RZ])
    have sub': "\<forall>i < length (map tl buf). set (map tl buf ! i) \<subseteq> Ss ! i"
    proof (intro allI impI)
      fix i assume i: "i < length (map tl buf)"
      then have i': "i < length buf" by simp
      have "set (tl (buf ! i)) \<subseteq> set (buf ! i)" by (cases "buf ! i") auto
      then show "set (map tl buf ! i) \<subseteq> Ss ! i" using SUB i' by auto
    qed
    have e1: "mbufn_take f (f (map hd buf) z) (map tl buf) = (w, buf')"
      using E1 False by simp
    have e2: "mbufn_take g (g (map2 (\<lambda>h a. h a) hs (map hd buf)) z') (map2 map hs (map tl buf))
        = (w2, buf2)"
    proof -
      have u: "mbufn_take g z' (map2 map hs buf)
          = mbufn_take g (g (map hd (map2 map hs buf)) z') (map tl (map2 map hs buf))"
        using ne by (subst mbufn_take.simps) simp
      have hd': "map hd (map2 map hs buf) = map2 (\<lambda>h a. h a) hs (map hd buf)"
        by (rule map2_map_hd[OF L1]) (use False in simp)
      have tl': "map tl (map2 map hs buf) = map2 map hs (map tl buf)"
        by (rule map2_map_tl[OF L1]) (use False in simp)
      have "mbufn_take g (g (map2 (\<lambda>h a. h a) hs (map hd buf)) z') (map2 map hs (map tl buf))
          = mbufn_take g (g (map hd (map2 map hs buf)) z') (map tl (map2 map hs buf))"
        by (simp only: hd' tl')
      also have "\<dots> = mbufn_take g z' (map2 map hs buf)" by (simp only: u)
      also have "\<dots> = (w2, buf2)" by (rule E2)
      finally show ?thesis .
    qed
    show ?thesis
      by (rule IH[OF False _ _ sub' STEP r e1 e2]) (use L1 L2 in simp_all)
  qed
qed

subsubsection \<open>Leftovers of a buffer\<close>

lemma mbuf2_take_sub:
  "mbuf2_take f (xs, ys) = (zs, (xs', ys')) \<Longrightarrow> set xs' \<subseteq> set xs \<and> set ys' \<subseteq> set ys"
proof (induct xs arbitrary: ys zs xs' ys')
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  note IH = Cons(1) and P = Cons(2)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using P by simp
  next
    case (Cons y ys0)
    obtain ws b1 b2 where w: "mbuf2_take f (xs, ys0) = (ws, (b1, b2))"
      by (cases "mbuf2_take f (xs, ys0)") auto
    have "xs' = b1" "ys' = b2" using P Cons w by simp_all
    then show ?thesis using IH[OF w] Cons by auto
  qed
qed

lemma set_tl_sub: "set (tl xs) \<subseteq> set xs"
  by (cases xs) auto

lemma mbufn_add_map2:
  "length hs = length buf \<Longrightarrow> length hs = length xss \<Longrightarrow>
     map2 map hs (mbufn_add xss buf) = mbufn_add (map2 map hs xss) (map2 map hs buf)"
proof (induct hs arbitrary: buf xss)
  case (Cons h hs)
  obtain b bs where b: "buf = b # bs" using Cons(2) by (cases buf) auto
  obtain x xs where x: "xss = x # xs" using Cons(3) by (cases xss) auto
  show ?case using Cons(1)[of bs xs] Cons(2,3) unfolding b x by simp
qed simp

lemma mbufn_take_sub:
  "mbufn_take f z buf = (w, buf') \<Longrightarrow>
     length buf' = length buf \<and> (\<forall>i < length buf. set (buf' ! i) \<subseteq> set (buf ! i))"
proof (induct f z buf arbitrary: w buf' rule: mbufn_take.induct)
  case (1 f z buf)
  note IH = 1(1) and E = 1(2)
  show ?case
  proof (cases "buf = [] \<or> [] \<in> set buf")
    case True
    have "(z, buf) = (w, buf')" using E by (subst (asm) mbufn_take.simps) (simp add: True)
    then show ?thesis by auto
  next
    case False
    have e: "mbufn_take f (f (map hd buf) z) (map tl buf) = (w, buf')"
      using E by (subst (asm) mbufn_take.simps) (simp add: False)
    have "length buf' = length (map tl buf) \<and>
        (\<forall>i < length (map tl buf). set (buf' ! i) \<subseteq> set (map tl buf ! i))"
      by (rule IH[OF False e])
    then show ?thesis using set_tl_sub by fastforce
  qed
qed

subsubsection \<open>Timestamped buffers\<close>

lemma mbufnt_take_sub:
  "mbufnt_take f z buf t0 ts = (w, buf', t', ts') \<Longrightarrow>
     length buf' = length buf \<and> (\<forall>i < length buf. set (buf' ! i) \<subseteq> set (buf ! i))"
proof (induct f z buf t0 ts arbitrary: w buf' t' ts' rule: mbufnt_take.induct)
  case (1 f z buf t0 ts)
  note IH = 1(1) and E = 1(2)
  show ?case
  proof (cases "[] \<in> set buf \<or> ts = []")
    case True
    have q: "mbufnt_take f z buf t0 ts = (z, buf, (case ts of [] \<Rightarrow> t0 | t # _ \<Rightarrow> t), ts)"
      using True by (subst mbufnt_take.simps) simp
    show ?thesis using E unfolding q by auto
  next
    case False
    have e: "mbufnt_take f (f (map hd buf) (hd ts) z) (map tl buf) (hd ts) (tl ts)
        = (w, buf', t', ts')"
      using E by (subst (asm) mbufnt_take.simps) (simp add: False)
    have "length buf' = length (map tl buf) \<and>
        (\<forall>i < length (map tl buf). set (buf' ! i) \<subseteq> set (map tl buf ! i))"
      by (rule IH[OF False e])
    then show ?thesis using set_tl_sub by fastforce
  qed
qed

lemma mbufnt_take_rel:
  "length hs = length buf \<Longrightarrow> length Ss = length buf \<Longrightarrow>
   (\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i) \<Longrightarrow>
   (\<And>as t u u'. length as = length hs \<Longrightarrow> (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> R u u' \<Longrightarrow>
      R (f as t u) (g (map2 (\<lambda>h a. h a) hs as) t u')) \<Longrightarrow>
   R z z' \<Longrightarrow>
   mbufnt_take f z buf t0 ts = (w, buf', t', ts') \<Longrightarrow>
   mbufnt_take g z' (map2 map hs buf) t0 ts = (w2, buf2, t2, ts2) \<Longrightarrow>
   R w w2 \<and> buf2 = map2 map hs buf' \<and> t2 = t' \<and> ts2 = ts'"
proof (induct f z buf t0 ts arbitrary: z' w buf' t' ts' w2 buf2 t2 ts2
    rule: mbufnt_take.induct)
  case (1 f z buf t0 ts)
  note IH = 1(1) and L1 = 1(2) and L2 = 1(3) and SUB = 1(4)
    and STEP = 1(5) and RZ = 1(6) and E1 = 1(7) and E2 = 1(8)
  show ?case
  proof (cases "[] \<in> set buf \<or> ts = []")
    case True
    then have ne': "[] \<in> set (map2 map hs buf) \<or> ts = []"
      by (simp only: map2_map_empty_iff[OF L1])
    have q1: "mbufnt_take f z buf t0 ts = (z, buf, (case ts of [] \<Rightarrow> t0 | t # _ \<Rightarrow> t), ts)"
      using True by (subst mbufnt_take.simps) simp
    have q2: "mbufnt_take g z' (map2 map hs buf) t0 ts
        = (z', map2 map hs buf, (case ts of [] \<Rightarrow> t0 | t # _ \<Rightarrow> t), ts)"
      using ne' by (subst mbufnt_take.simps) simp
    show ?thesis using E1 E2 RZ unfolding q1 q2 by auto
  next
    case False
    then have ne: "\<not> ([] \<in> set (map2 map hs buf) \<or> ts = [])"
      by (simp only: map2_map_empty_iff[OF L1]) simp
    have las: "length (map hd buf) = length hs" using L1 by simp
    have mem: "\<forall>i < length (map hd buf). map hd buf ! i \<in> Ss ! i"
    proof (intro allI impI)
      fix i assume i: "i < length (map hd buf)"
      then have i': "i < length buf" by simp
      then have "buf ! i \<noteq> []" using False by (auto simp: in_set_conv_nth)
      then have "hd (buf ! i) \<in> set (buf ! i)" by simp
      then show "map hd buf ! i \<in> Ss ! i" using SUB i' by auto
    qed
    have r: "R (f (map hd buf) (hd ts) z) (g (map2 (\<lambda>h a. h a) hs (map hd buf)) (hd ts) z')"
      by (rule STEP[OF las mem RZ])
    have sub': "\<forall>i < length (map tl buf). set (map tl buf ! i) \<subseteq> Ss ! i"
    proof (intro allI impI)
      fix i assume i: "i < length (map tl buf)"
      then have i': "i < length buf" by simp
      have "set (tl (buf ! i)) \<subseteq> set (buf ! i)" by (cases "buf ! i") auto
      then show "set (map tl buf ! i) \<subseteq> Ss ! i" using SUB i' by auto
    qed
    have e1: "mbufnt_take f (f (map hd buf) (hd ts) z) (map tl buf) (hd ts) (tl ts)
        = (w, buf', t', ts')"
      using E1 False by simp
    have e2: "mbufnt_take g (g (map2 (\<lambda>h a. h a) hs (map hd buf)) (hd ts) z')
        (map2 map hs (map tl buf)) (hd ts) (tl ts) = (w2, buf2, t2, ts2)"
    proof -
      have u: "mbufnt_take g z' (map2 map hs buf) t0 ts
          = mbufnt_take g (g (map hd (map2 map hs buf)) (hd ts) z')
              (map tl (map2 map hs buf)) (hd ts) (tl ts)"
        using ne by (subst mbufnt_take.simps) simp
      have hd': "map hd (map2 map hs buf) = map2 (\<lambda>h a. h a) hs (map hd buf)"
        by (rule map2_map_hd[OF L1]) (use False in simp)
      have tl': "map tl (map2 map hs buf) = map2 map hs (map tl buf)"
        by (rule map2_map_tl[OF L1]) (use False in simp)
      show ?thesis using E2 unfolding u hd' tl' .
    qed
    show ?thesis
      by (rule IH[OF False _ _ sub' STEP r e1 e2]) (use L1 L2 in simp_all)
  qed
qed

lemma mprev_next_sub: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow> set xs' \<subseteq> set xs"
  by (induct I xs ts arbitrary: ys xs' ts' rule: mprev_next.induct)
    (auto split: prod.splits)

subsection \<open>Multi-way join of the monitor\<close>

lemma etabc_unit_table: "etabc [] [] unit_table = unit_table"
  by (simp add: etabc_def unit_table_def)

lemma map2_append:
  "length as = length xs \<Longrightarrow> map2 f (as @ bs) (xs @ ys) = map2 f as xs @ map2 f bs ys"
  by simp

lemma finite_kands_pos:
  "finite T \<Longrightarrow> \<forall>(k, u) \<in> set us. finite u \<Longrightarrow> finite (kands_pos acc T us)"
  by (induct us arbitrary: acc T) (auto simp: finite_join)

lemma wf_operands_zip:
  assumes "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Us"
  shows "\<forall>(k, u) \<in> set (zip (map fst kcs) Us). distinct k \<and> table k u \<and> finite u"
    and "length (map fst kcs) = length Us"
    and "list_all2 eframe (map fst kcs) (map snd kcs)"
  using assms by (auto simp: list_all2_conv_all_nth set_zip wf_operand_def case_prod_beta
      eframe_def)

theorem gmulti_join_eq:
  assumes f0: "eframe k0 c0" and t0: "table k0 T0" and fT0: "finite T0"
    and pos: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Us"
    and neg: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) nkcs Vs"
    and sub: "\<forall>c \<in> set (map snd nkcs). set c \<subseteq> set (eands_cols c0 (map snd kcs))"
    and cs: "distinct cs" "set cs = set (kands_cols k0 (map fst kcs))"
  shows "gmulti_join (eands_plans c0 (map snd kcs))
           (eands_plans (eands_cols c0 (map snd kcs)) (map snd nkcs))
           (map2 (\<lambda>(k, c). etabc k c) ((k0, c0) # kcs @ nkcs) ((T0 # Us) @ Vs))
       = etabc cs (eands_cols c0 (map snd kcs))
           (mmulti_join cs (k0 # map fst kcs) (map fst nkcs) ((T0 # Us) @ Vs))"
proof -
  let ?K = "kands_cols k0 (map fst kcs)" and ?C = "eands_cols c0 (map snd kcs)"
  let ?P = "kands_pos k0 T0 (zip (map fst kcs) Us)"
  have lp: "length kcs = length Us" using pos by (rule list_all2_lengthD)
  have ln: "length nkcs = length Vs" using neg by (rule list_all2_lengthD)
  note wp = wf_operands_zip[OF pos] and wn = wf_operands_zip[OF neg]
  have dk0: "distinct k0" using eframeD(1)[OF f0] .
  have fK: "eframe ?K ?C" by (rule eframe_eands_cols[OF wp(3) f0])
  have wp1: "\<forall>(k, u) \<in> set (zip (map fst kcs) Us). distinct k \<and> table k u" using wp(1) by auto
  have tP: "table ?K ?P"
    unfolding table_def using kands_pos_iff[OF dk0 t0 wp1] wp(2) by simp
  have fP: "finite ?P" by (rule finite_kands_pos[OF fT0]) (use wp(1) in auto)
  have subK: "\<forall>(k, u) \<in> set (zip (map fst nkcs) Vs). distinct k \<and> table k u \<and> set k \<subseteq> set ?K"
  proof (intro ballI, clarify)
    fix k u assume ku: "(k, u) \<in> set (zip (map fst nkcs) Vs)"
    then obtain i where i: "i < length nkcs" "k = fst (nkcs ! i)" "u = Vs ! i"
      using ln by (auto simp: in_set_zip)
    have "eframe k (snd (nkcs ! i))" using wn(3) i by (auto simp: list_all2_conv_all_nth)
    moreover have "set (snd (nkcs ! i)) \<subseteq> set ?C" using sub i by auto
    moreover have "set ?C = set ?K" using eframeD(3)[OF fK] .
    ultimately show "distinct k \<and> table k u \<and> set k \<subseteq> set ?K"
      using wn(1) ku by (auto simp: eframe_def)
  qed
  have m: "map2 (\<lambda>(k, c). etabc k c) ((k0, c0) # kcs @ nkcs) ((T0 # Us) @ Vs)
      = etabc k0 c0 T0 # (map2 (\<lambda>(k, c). etabc k c) kcs Us @ map2 (\<lambda>(k, c). etabc k c) nkcs Vs)"
    by (simp add: map2_append[OF lp])
  have "gmulti_join (eands_plans c0 (map snd kcs)) (eands_plans ?C (map snd nkcs))
          (map2 (\<lambda>(k, c). etabc k c) ((k0, c0) # kcs @ nkcs) ((T0 # Us) @ Vs))
      = gands_neg (eands_plans ?C (map snd nkcs))
          (gands_pos (eands_plans c0 (map snd kcs)) (etabc k0 c0 T0)
            (map2 (\<lambda>(k, c). etabc k c) kcs Us))
          (map2 (\<lambda>(k, c). etabc k c) nkcs Vs)"
    unfolding gmulti_join_def m using lp by simp
  also have "\<dots> = gands_neg (eands_plans ?C (map snd nkcs)) (etabc ?K ?C ?P)
      (map2 (\<lambda>(k, c). etabc k c) nkcs Vs)"
    by (simp only: gands_pos_dtabc[OF f0 t0 fT0 pos])
  also have "\<dots> = etabc ?K ?C (kands_neg ?K ?P (zip (map fst nkcs) Vs))"
    by (rule gands_neg_dtabc[OF fK tP fP neg sub])
  also have "\<dots> = etabc cs ?C (restrict cs ?K ` kands_neg ?K ?P (zip (map fst nkcs) Vs))"
  proof -
    have "table ?K (kands_neg ?K ?P (zip (map fst nkcs) Vs))"
      using kands_neg_iff[OF eframeD(1)[OF fK] tP subK] tP by (auto simp: table_def)
    then show ?thesis by (rule etabc_restrict[OF fK cs(2), symmetric])
  qed
  also have "\<dots> = etabc cs ?C (mmulti_join cs (k0 # map fst kcs) (map fst nkcs) ((T0 # Us) @ Vs))"
  proof -
    have "mmulti_join cs (k0 # map fst kcs) (map fst nkcs) ((T0 # Us) @ Vs)
        = restrict cs ?K ` kands_neg ?K ?P (zip (map fst nkcs) Vs)"
      by (rule mmulti_join_kands[OF dk0 t0 wp1 wp(2) subK _ cs]) (simp add: ln)
    then show ?thesis by (simp only:)
  qed
  finally show ?thesis .
qed

subsection \<open>Constraints, assignment and time terms\<close>

theorem ueval_constraint_reindex:
  assumes fv1: "Formula.fv_trm t1 \<subseteq> set cs" and fv2: "Formula.fv_trm t2 \<subseteq> set cs"
  shows "etabc ks cs (Set.filter (eval_constraint ks (t1, p, c, t2)) T)
       = Set.filter (ueval_constraint (reindex_constraint cs (t1, p, c, t2))) (etabc ks cs T)"
proof -
  have "ueval_constraint (reindex_constraint cs (t1, p, c, t2)) (restrict cs ks x)
      = eval_constraint ks (t1, p, c, t2) x" for x
    by (simp add: reindex_constraint_def ueval_constraint_def
        umeval_trm_reindex[OF fv1] umeval_trm_reindex[OF fv2])
  then show ?thesis unfolding etabc_def by auto
qed

text \<open>The kernel's assignment appends the value to its tuple; the short tuple inserts it at the
  new column's position @{const ins_pos} in the merged column list.\<close>

lemma restrict_merge_single_append:
  assumes s: "sorted_wrt (<) cs" and yg: "y \<notin> set ks" and sub: "set cs \<subseteq> set ks"
    and w: "wf_tuple ks x"
  shows "restrict (merge_cols cs [y]) (ks @ [y]) (x @ [v])
       = take (ins_pos cs y) (restrict cs ks x) @ v # drop (ins_pos cs y) (restrict cs ks x)"
proof -
  have "restrict (merge_cols cs [y]) (ks @ [y]) (x @ [v]) = restrict (merge_cols cs [y]) (y # ks) (v # x)"
    using yg sub by (intro restrict_cong) (auto simp: tup_get_append[OF w] tup_get_Cons set_merge_cols)
  also have "\<dots> = take (ins_pos cs y) (restrict cs ks x) @ v # drop (ins_pos cs y) (restrict cs ks x)"
    using yg sub by (intro restrict_merge_single[OF s]) auto
  finally show ?thesis .
qed

theorem uassign_eval_assignment:
  assumes f: "eframe ks cs" and y: "y \<notin> set ks" and fv: "Formula.fv_trm t \<subseteq> set cs"
    and tT: "table ks T"
  shows "uassign (ins_pos cs y) (reindex_trm cs t) (etabc ks cs T)
       = etabc (ks @ [y]) (merge_cols cs [y]) (eval_assignment ks (y, t) ` T)"
proof -
  have "uassign1 (ins_pos cs y) (reindex_trm cs t) (restrict cs ks x)
      = restrict (merge_cols cs [y]) (ks @ [y]) (eval_assignment ks (y, t) x)" if "x \<in> T" for x
  proof -
    have w: "wf_tuple ks x" using tT that by (simp add: table_def)
    show ?thesis
      unfolding uassign1_def eval_assignment.simps umeval_trm_reindex[OF fv]
      by (rule restrict_merge_single_append[symmetric, OF eframeD(2)[OF f] y _ w])
        (use eframeD(3)[OF f] in simp)
  qed
  then show ?thesis unfolding uassign_def etabc_def image_image by (auto intro!: image_cong)
qed

theorem umtrm_eval_mtrm: "umtrm mt x = eval_mtrm mt x"
  by (cases mt) (simp_all add: singleton_table_def unit_table_def empty_table_def)

subsection \<open>Trigger structure over ascending columns\<close>

text \<open>The structure reads its answer off the auxiliary list, so @{const trigger_results} itself
  has to commute with the reordering.\<close>

lemma trigger_results_eq:
  "trigger_results args cur auxlist =
     (if 0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist)
      then (args_R args, {tuple. wf_tuple (args_R args) tuple \<and>
        (\<forall>i < length auxlist. mem (args_ivl args) (cur - fst (auxlist ! i)) \<longrightarrow>
           (tuple \<in> snd (snd (auxlist ! i)) \<or>
            (\<exists>j. i < j \<and> j < length auxlist \<and>
               join_cond (args_pos args) (fst (snd (auxlist ! j)))
                 (restrict (args_L args) (args_R args) tuple))))})
      else ([], unit_table))"
  by (auto simp: Let_def case_prod_beta)

lemma length_filter_eauxlist3:
  "length (filter (\<lambda>(t, _, _). P t) (eauxlist3 kL cL kR cR auxlist))
     = length (filter (\<lambda>(t, _, _). P t) auxlist)"
  by (induct auxlist) (auto simp: eauxlist3_def)

lemma nth_eauxlist3:
  "i < length auxlist \<Longrightarrow> eauxlist3 kL cL kR cR auxlist ! i =
     (fst (auxlist ! i), etabc kL cL (fst (snd (auxlist ! i))), etabc kR cR (snd (snd (auxlist ! i))))"
  by (simp add: eauxlist3_def case_prod_beta)

theorem etabc_trigger_results:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and wf: "\<forall>(t, l, r) \<in> set auxlist. table kL l \<and> table kR r"
  shows "eframe (fst (trigger_results args cur auxlist))
           (fst (trigger_results (eargs cR cL args) cur (eauxlist3 kL cL kR cR auxlist)))"
    and "snd (trigger_results (eargs cR cL args) cur (eauxlist3 kL cL kR cR auxlist))
       = etabc (fst (trigger_results args cur auxlist))
           (fst (trigger_results (eargs cR cL args) cur (eauxlist3 kL cL kR cR auxlist)))
           (snd (trigger_results args cur auxlist))"
proof -
  let ?I = "args_ivl args" and ?p = "args_pos args"
  let ?da = "eauxlist3 kL cL kR cR auxlist"
  have sub': "set cL \<subseteq> set cR" using sub eframeD(3)[OF fR] eframeD(3)[OF fL] by simp
  have tl: "table kL (fst (snd (auxlist ! i)))" and tr: "table kR (snd (snd (auxlist ! i)))"
    if "i < length auxlist" for i
    using wf nth_mem[OF that] by (auto simp: case_prod_beta)
  have key: "restrict cL cR (restrict cR kR a) = restrict cL kL (restrict kL kR a)" for a :: "event_data tuple"
    using sub sub' eframeD(3)[OF fR] eframeD(3)[OF fL] by (simp add: restrict_restrict)
  define P where "P a \<longleftrightarrow> (\<forall>i < length auxlist. mem ?I (cur - fst (auxlist ! i)) \<longrightarrow>
      (a \<in> snd (snd (auxlist ! i)) \<or>
       (\<exists>j. i < j \<and> j < length auxlist \<and>
          join_cond ?p (fst (snd (auxlist ! j))) (restrict kL kR a))))" for a :: "event_data tuple"
  define Q where "Q d \<longleftrightarrow> (\<forall>i < length auxlist. mem ?I (cur - fst (auxlist ! i)) \<longrightarrow>
      (d \<in> etabc kR cR (snd (snd (auxlist ! i))) \<or>
       (\<exists>j. i < j \<and> j < length auxlist \<and>
          join_cond ?p (etabc kL cL (fst (snd (auxlist ! j)))) (restrict cL cR d))))"
    for d :: "event_data tuple"
  have cond: "Q (restrict cR kR a) = P a" if wa: "wf_tuple kR a" for a :: "event_data tuple"
  proof -
    have inR: "(restrict cR kR a \<in> etabc kR cR (snd (snd (auxlist ! i)))) = (a \<in> snd (snd (auxlist ! i)))"
      if "i < length auxlist" for i
      by (rule etabc_in_iff[OF fR tr[OF that] wa])
    have inL: "(restrict cL cR (restrict cR kR a) \<in> etabc kL cL (fst (snd (auxlist ! j))))
        = (restrict kL kR a \<in> fst (snd (auxlist ! j)))" if "j < length auxlist" for j
      unfolding key by (rule etabc_in_iff[OF fL tl[OF that]]) simp
    show ?thesis unfolding P_def Q_def by (auto simp: inR inL)
  qed
  have DS: "{d. wf_tuple cR d \<and> Q d} = etabc kR cR {a. wf_tuple kR a \<and> P a}"
  proof (intro set_eqI iffI)
    fix d assume d: "d \<in> {d. wf_tuple cR d \<and> Q d}"
    let ?a = "restrict kR cR d"
    have ld: "length d = length cR" using d by (simp add: wf_tuple_def)
    have da: "restrict cR kR ?a = d" by (rule restrict_inv'[OF fR ld])
    have "P ?a" using d cond[of ?a] da by simp
    then have "?a \<in> {a. wf_tuple kR a \<and> P a}" by simp
    then show "d \<in> etabc kR cR {a. wf_tuple kR a \<and> P a}"
      unfolding etabc_def using da by (metis image_eqI)
  next
    fix d assume "d \<in> etabc kR cR {a. wf_tuple kR a \<and> P a}"
    then obtain a where a: "wf_tuple kR a" "P a" and da: "d = restrict cR kR a"
      unfolding etabc_def by auto
    show "d \<in> {d. wf_tuple cR d \<and> Q d}" using cond[OF a(1)] a(2) da by simp
  qed
  have flt: "length (filter (\<lambda>(t, _, _). mem ?I (cur - t)) ?da)
      = length (filter (\<lambda>(t, _, _). mem ?I (cur - t)) auxlist)"
    by (rule length_filter_eauxlist3)
  have dset: "{tuple. wf_tuple cR tuple \<and>
      (\<forall>i < length ?da. mem ?I (cur - fst (?da ! i)) \<longrightarrow>
         (tuple \<in> snd (snd (?da ! i)) \<or>
          (\<exists>j. i < j \<and> j < length ?da \<and>
             join_cond ?p (fst (snd (?da ! j))) (restrict cL cR tuple))))}
    = {d. wf_tuple cR d \<and> Q d}"
    by (auto simp: Q_def nth_eauxlist3)
  have dsimp: "trigger_results (eargs cR cL args) cur ?da
      = (if 0 < length (filter (\<lambda>(t, _, _). mem ?I (cur - t)) auxlist)
         then (cR, {d. wf_tuple cR d \<and> Q d}) else ([], unit_table))"
    by (simp only: trigger_results_eq flt eargs_simps dset)
  have ssimp: "trigger_results args cur auxlist
      = (if 0 < length (filter (\<lambda>(t, _, _). mem ?I (cur - t)) auxlist)
         then (kR, {a. wf_tuple kR a \<and> P a}) else ([], unit_table))"
    by (simp only: trigger_results_eq aL aR P_def)
  show "eframe (fst (trigger_results args cur auxlist))
      (fst (trigger_results (eargs cR cL args) cur ?da))"
    unfolding dsimp ssimp using fR by (simp add: eframe_def)
  show "snd (trigger_results (eargs cR cL args) cur ?da)
       = etabc (fst (trigger_results args cur auxlist)) (fst (trigger_results (eargs cR cL args) cur ?da))
           (snd (trigger_results args cur auxlist))"
    unfolding dsimp ssimp using DS by (simp add: etabc_unit_table)
qed

lemma eauxlist3_filter_append:
  "eauxlist3 kL cL kR cR (filter (\<lambda>(t, _). P t) auxlist @ [(nt, l, r)])
     = filter (\<lambda>(t, _). P t) (eauxlist3 kL cL kR cR auxlist) @ [(nt, etabc kL cL l, etabc kR cR r)]"
  by (induct auxlist) (auto simp: eauxlist3_def)

lemma mbuf2T_take_rel:
  "(\<And>a b t u za z'a. a \<in> set xs \<Longrightarrow> b \<in> set ys \<Longrightarrow> R u za z'a \<Longrightarrow> u \<le> t \<Longrightarrow>
      R t (f a b t za) (g (h a) (k b) t z'a)) \<Longrightarrow>
   R u0 z z' \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. u0 \<le> t) \<Longrightarrow> (\<forall>t \<in> set ts. t \<le> tb) \<Longrightarrow> u0 \<le> tb \<Longrightarrow>
   mbuf2T_take f z (xs, ys) ts = (w, (xs', ys'), ts') \<Longrightarrow>
   mbuf2T_take g z' (map h xs, map k ys) ts = (w2, buf2, ts2) \<Longrightarrow>
   (\<exists>u. R u w w2 \<and> u \<le> tb \<and> (\<forall>t \<in> set ts'. u \<le> t)) \<and> sorted ts' \<and>
     set ts' \<subseteq> set ts \<and> set xs' \<subseteq> set xs \<and> set ys' \<subseteq> set ys \<and>
     buf2 = (map h xs', map k ys') \<and> ts2 = ts'"
proof (induct xs arbitrary: ys z z' u0 ts w xs' ys' ts' w2 buf2 ts2)
  case Nil
  then show ?case by (cases ts) (auto intro!: exI[of _ u0])
next
  case (Cons x xs)
  note IH = Cons(1) and P1 = Cons(2) and P2 = Cons(3) and P3 = Cons(4)
    and P4 = Cons(5) and P5 = Cons(6) and P6 = Cons(7) and P7 = Cons(8) and P8 = Cons(9)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using P2 P3 P4 P6 P7 P8 by (cases ts) (auto intro!: exI[of _ u0])
  next
    case (Cons y ys2)
    note ysC = Cons
    show ?thesis
    proof (cases ts)
      case Nil
      then show ?thesis using P2 P6 P7 P8 ysC by (auto intro!: exI[of _ u0])
    next
      case (Cons t ts3)
      note tsC = Cons
      have ut: "u0 \<le> t" using P4 tsC by simp
      have r: "R t (f x y t z) (g (h x) (k y) t z')"
        using P1[of x y u0 z z' t] P2 ut ysC by simp
      have p1: "\<And>a b t' u za z'a. a \<in> set xs \<Longrightarrow> b \<in> set ys2 \<Longrightarrow> R u za z'a \<Longrightarrow> u \<le> t' \<Longrightarrow>
          R t' (f a b t' za) (g (h a) (k b) t' z'a)" using P1 ysC by simp
      have s1: "mbuf2T_take f (f x y t z) (xs, ys2) ts3 = (w, (xs', ys'), ts')"
        using P7 ysC tsC by simp
      have s2: "mbuf2T_take g (g (h x) (k y) t z') (map h xs, map k ys2) ts3
          = (w2, buf2, ts2)"
        using P8 ysC tsC by simp
      have "(\<exists>u. R u w w2 \<and> u \<le> tb \<and> (\<forall>t' \<in> set ts'. u \<le> t')) \<and> sorted ts' \<and>
          set ts' \<subseteq> set ts3 \<and> set xs' \<subseteq> set xs \<and> set ys' \<subseteq> set ys2 \<and>
          buf2 = (map h xs', map k ys') \<and> ts2 = ts'"
        by (rule IH[OF p1 r _ _ _ _ s1 s2]) (use P3 P5 P6 tsC in auto)
      then show ?thesis using tsC ysC by auto
    qed
  qed
qed

subsection \<open>Index for the semi-join\<close>

lemma in_set_of_idx: "(y \<in> set_of_idx m) = (\<exists>k Y. Mapping.lookup m k = Some Y \<and> y \<in> Y)"
  by transfer (auto simp: ran_def)

theorem esemi_idx_dsemi: "esemi_idx msk pos (eidx msk T) X = esemi msk pos T X"
proof (intro set_eqI iffI)
  fix y assume "y \<in> esemi_idx msk pos (eidx msk T) X"
  then show "y \<in> esemi msk pos T X"
    by (auto simp: esemi_idx_def esemi_def in_set_of_idx Mapping.lookup_filter lookup_eidx
        split: if_splits option.splits)
next
  fix y assume "y \<in> esemi msk pos T X"
  then have yT: "y \<in> T" and yp: "(eproj msk y \<in> X) = pos" by (auto simp: esemi_def)
  have "Mapping.lookup (Mapping.filter (\<lambda>k _. (k \<in> X) = pos) (eidx msk T)) (eproj msk y)
      = Some {z \<in> T. eproj msk z = eproj msk y}"
    using yT yp by (simp add: Mapping.lookup_filter lookup_eidx)
  then show "y \<in> esemi_idx msk pos (eidx msk T) X"
    using yT by (auto simp: esemi_idx_def in_set_of_idx)
qed

(*<*)
end
(*>*)
