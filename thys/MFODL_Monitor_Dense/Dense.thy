(*<*)
theory Dense
  imports Dense_Utuple
begin
(*>*)

section \<open>Tables over ascending columns: the verified core\<close>

text \<open>
  A table of the kernel is a set of tuples over a list of columns, the free variables of the
  subformula that produced it in the order of @{const Formula.fv_list}.  The dense monitor keeps
  the same tables over the same columns in ascending order: its joins merge two column lists
  instead of looking them up, and its plans are computed once from the two lists.  A kernel
  tuple over @{term ks} becomes the dense tuple over @{term cs} by reading it at the columns in
  their ascending order, @{term "restrict cs ks x"}.

  This theory proves that the reordering loses nothing -- it is a bijection between the tables
  over the two column lists -- and that the dense operations over the ascending columns agree
  with the kernel's over its own.
\<close>

type_synonym cols = "nat list"

text \<open>A dense frame: the kernel's column list of a table, and the same columns in ascending
  order.\<close>

definition dframe :: "cols \<Rightarrow> cols \<Rightarrow> bool" where
  "dframe ks cs \<longleftrightarrow> distinct ks \<and> sorted_wrt (<) cs \<and> set cs = set ks"

lemma dframeD:
  assumes "dframe ks cs"
  shows "distinct ks" "sorted_wrt (<) cs" "set cs = set ks" "distinct cs"
  using assms by (auto simp: dframe_def strict_sorted_iff)

text \<open>The dense projection by a mask, used between dense frames.\<close>

fun dproj :: "bool list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "dproj [] xs = []"
| "dproj (True # bs) (x # xs) = x # dproj bs xs"
| "dproj (False # bs) (x # xs) = dproj bs xs"
| "dproj (b # bs) [] = []"

subsection \<open>The representation relation\<close>

definition dtabc :: "cols \<Rightarrow> cols \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "dtabc ks cs T = restrict cs ks ` T"

definition dtabw :: "cols \<Rightarrow> cols \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "dtabw ks cs D = restrict ks cs ` D"

definition dtable :: "cols \<Rightarrow> 'b list set \<Rightarrow> bool" where
  "dtable cs D \<longleftrightarrow> (\<forall>d \<in> D. length d = length cs)"

lemma dtable_table: "dtable cs D = table cs D"
  by (simp add: dtable_def table_def wf_tuple_def)

lemma restrict_map: "restrict cs ks x = map (tup_get ks x) cs"
  by (simp add: restrict_def)

lemma restrict_inv:
  assumes "dframe ks cs" "wf_tuple ks x"
  shows "restrict ks cs (restrict cs ks x) = x"
  using assms by (simp add: dframe_def restrict_restrict restrict_idle)

lemma restrict_inv':
  assumes "dframe ks cs" "length d = length cs"
  shows "restrict cs ks (restrict ks cs d) = d"
  using assms dframeD(4)[OF assms(1)]
  by (simp add: dframe_def restrict_restrict restrict_idle wf_tuple_def)

lemma inj_on_restrict:
  "dframe ks cs \<Longrightarrow> inj_on (restrict cs ks) {x. wf_tuple ks x}"
  by (rule inj_onI) (metis mem_Collect_eq restrict_inv)

lemma dtabc_in_iff:
  "dframe ks cs \<Longrightarrow> table ks T \<Longrightarrow> wf_tuple ks x \<Longrightarrow> (restrict cs ks x \<in> dtabc ks cs T) = (x \<in> T)"
  using inj_on_restrict[of ks cs] by (auto simp: dtabc_def table_def inj_on_def)

lemma dtable_dtabc: "dtable cs (dtabc ks cs T)"
  by (auto simp: dtable_def dtabc_def)

lemma dtabw_dtabc: "dframe ks cs \<Longrightarrow> table ks T \<Longrightarrow> dtabw ks cs (dtabc ks cs T) = T"
  by (force simp: dtabw_def dtabc_def table_def restrict_inv image_image)

lemma dtabc_empty[simp]: "dtabc ks cs {} = {}"
  by (simp add: dtabc_def)

lemma dtabc_empty_iff: "(dtabc ks cs T = {}) = (T = {})"
  by (auto simp: dtabc_def)

lemma dtabc_Un_img: "dtabc ks cs (A \<union> B) = dtabc ks cs A \<union> dtabc ks cs B"
  by (auto simp: dtabc_def)

lemma finite_dtabc: "finite T \<Longrightarrow> finite (dtabc ks cs T)"
  by (simp add: dtabc_def)

text \<open>A frame that is already ascending is left alone.\<close>

lemma dtabc_same: "distinct cs \<Longrightarrow> table cs T \<Longrightarrow> dtabc cs cs T = T"
  by (force simp: dtabc_def table_def restrict_idle)

subsection \<open>Merging two column lists\<close>

datatype mrg = MLft | MRgt | MBth

fun mrg_plan :: "cols \<Rightarrow> cols \<Rightarrow> mrg list" where
  "mrg_plan [] ds = map (\<lambda>_. MRgt) ds"
| "mrg_plan (c # cs) [] = MLft # mrg_plan cs []"
| "mrg_plan (c # cs) (d # ds) =
    (if c < d then MLft # mrg_plan cs (d # ds)
     else if d < c then MRgt # mrg_plan (c # cs) ds
     else MBth # mrg_plan cs ds)"

fun merge_cols :: "cols \<Rightarrow> cols \<Rightarrow> cols" where
  "merge_cols [] ds = ds"
| "merge_cols (c # cs) [] = c # merge_cols cs []"
| "merge_cols (c # cs) (d # ds) =
    (if c < d then c # merge_cols cs (d # ds)
     else if d < c then d # merge_cols (c # cs) ds
     else c # merge_cols cs ds)"

fun djoin1 :: "mrg list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list option" where
  "djoin1 [] xs ys = Some []"
| "djoin1 (MLft # p) (x # xs) ys = map_option (Cons x) (djoin1 p xs ys)"
| "djoin1 (MRgt # p) xs (y # ys) = map_option (Cons y) (djoin1 p xs ys)"
| "djoin1 (MBth # p) (x # xs) (y # ys) =
    (if x = y then map_option (Cons x) (djoin1 p xs ys) else None)"
| "djoin1 (m # p) xs ys = None"

lemma djoin1_all_MRgt: "djoin1 (map (\<lambda>_. MRgt) ds) xs (map g ds) = Some (map g ds)"
  by (induct ds arbitrary: xs) auto

lemma djoin1_all_MLft: "djoin1 (mrg_plan cs []) (map f cs) ys = Some (map f cs)"
  by (induct cs arbitrary: ys) auto

lemma merge_cols_Nil2: "merge_cols cs [] = cs"
  by (induct cs) auto

lemma set_merge_cols: "set (merge_cols cs ds) = set cs \<union> set ds"
  by (induct cs ds rule: merge_cols.induct) auto

lemma sorted_merge_cols:
  "sorted_wrt (<) cs \<Longrightarrow> sorted_wrt (<) ds \<Longrightarrow> sorted_wrt (<) (merge_cols cs ds)"
  by (induct cs ds rule: merge_cols.induct) (auto simp: set_merge_cols)

text \<open>The short join is a merge driven by the two column lists: it succeeds exactly when the
  two tuples agree on the shared columns, and then reads each merged column from the side that
  has it.\<close>

lemma djoin1_mrg_plan:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow>
   djoin1 (mrg_plan cs1 cs2) (map f cs1) (map g cs2) =
     (if \<forall>c \<in> set cs1 \<inter> set cs2. f c = g c
      then Some (map (\<lambda>c. if c \<in> set cs1 then f c else g c) (merge_cols cs1 cs2))
      else None)"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: djoin1_all_MRgt cong: map_cong)
next
  case (2 c cs)
  then show ?case by (simp add: djoin1_all_MLft merge_cols_Nil2 cong: map_cong)
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

lemma dframe_merge:
  "dframe ks1 cs1 \<Longrightarrow> dframe ks2 cs2 \<Longrightarrow> dframe (cols_union ks1 ks2) (merge_cols cs1 cs2)"
  by (auto simp: dframe_def sorted_merge_cols set_merge_cols)

text \<open>The kernel's join of two tuples reads every column of the result from the side that has
  it.\<close>

lemma tup_get_join1:
  assumes "wf_tuple ks1 x" "join1 ks1 ks2 (x, y) = Some z" "c \<in> set ks1 \<union> set ks2"
  shows "tup_get (cols_union ks1 ks2) z c = (if c \<in> set ks1 then tup_get ks1 x c else tup_get ks2 y c)"
  using assms
  by (auto simp: join1.simps cols_union_def tup_get_append tup_get_restrict split: if_splits)

lemma join1_iff:
  "join1 ks1 ks2 (x, y) \<noteq> None \<longleftrightarrow> (\<forall>c \<in> set ks1 \<inter> set ks2. tup_get ks1 x c = tup_get ks2 y c)"
  by (simp add: join1.simps)

lemma djoin1_join1:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2"
    and w1: "wf_tuple ks1 x"
  shows "djoin1 (mrg_plan cs1 cs2) (restrict cs1 ks1 x) (restrict cs2 ks2 y)
       = map_option (restrict (merge_cols cs1 cs2) (cols_union ks1 ks2)) (join1 ks1 ks2 (x, y))"
proof -
  note s1 = dframeD(2)[OF f1] and s2 = dframeD(2)[OF f2]
  have set1: "set cs1 = set ks1" and set2: "set cs2 = set ks2"
    using f1 f2 by (simp_all add: dframe_def)
  show ?thesis
  proof (cases "join1 ks1 ks2 (x, y)")
    case None
    then show ?thesis
      using join1_iff[of ks1 ks2 x y]
      by (simp add: restrict_map djoin1_mrg_plan[OF s1 s2] set1 set2)
  next
    case (Some z)
    then have ag: "\<forall>c \<in> set ks1 \<inter> set ks2. tup_get ks1 x c = tup_get ks2 y c"
      using join1_iff[of ks1 ks2 x y] by simp
    have "map (\<lambda>c. if c \<in> set cs1 then tup_get ks1 x c else tup_get ks2 y c) (merge_cols cs1 cs2)
        = map (tup_get (cols_union ks1 ks2) z) (merge_cols cs1 cs2)"
      using tup_get_join1[OF w1 Some] by (auto simp: set_merge_cols set1 set2)
    then show ?thesis
      using Some ag by (simp add: restrict_map djoin1_mrg_plan[OF s1 s2] set1 set2)
  qed
qed

text \<open>The short join of two tables is the short form of the kernel's join.\<close>

lemma dtabc_join:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2"
    and t1: "table ks1 T"
  shows "dtabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T True ks2 T')
       = (\<Union>a \<in> dtabc ks1 cs1 T. \<Union>b \<in> dtabc ks2 cs2 T'.
            set_option (djoin1 (mrg_plan cs1 cs2) a b))"
proof -
  have key: "\<And>a b. a \<in> T \<Longrightarrow>
      djoin1 (mrg_plan cs1 cs2) (restrict cs1 ks1 a) (restrict cs2 ks2 b)
        = map_option (restrict (merge_cols cs1 cs2) (cols_union ks1 ks2)) (join1 ks1 ks2 (a, b))"
    using t1 by (intro djoin1_join1[OF f1 f2]) (auto simp: table_def)
  have "dtabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T True ks2 T')
      = (\<Union>a \<in> T. \<Union>b \<in> T'. restrict (merge_cols cs1 cs2) (cols_union ks1 ks2) `
           set_option (join1 ks1 ks2 (a, b)))"
    unfolding dtabc_def join_True_code by blast
  also have "\<dots> = (\<Union>a \<in> T. \<Union>b \<in> T'. set_option
      (djoin1 (mrg_plan cs1 cs2) (restrict cs1 ks1 a) (restrict cs2 ks2 b)))"
    by (intro SUP_cong refl) (auto simp: key split: option.splits)
  also have "\<dots> = (\<Union>a \<in> dtabc ks1 cs1 T. \<Union>b \<in> dtabc ks2 cs2 T'.
      set_option (djoin1 (mrg_plan cs1 cs2) a b))"
    unfolding dtabc_def by blast
  finally show ?thesis .
qed

text \<open>A kernel table read in another order of its columns has the same dense form.\<close>

lemma dtabc_restrict:
  assumes "dframe ks cs" "set ks' = set ks" "table ks T"
  shows "dtabc ks' cs (restrict ks' ks ` T) = dtabc ks cs T"
  using assms by (force simp: dtabc_def dframe_def image_image restrict_restrict)

subsection \<open>Projecting a short tuple onto a sublist of its columns\<close>

fun mrg_left_key :: "mrg list \<Rightarrow> bool list" where
  "mrg_left_key [] = []"
| "mrg_left_key (MLft # p) = False # mrg_left_key p"
| "mrg_left_key (MRgt # p) = mrg_left_key p"
| "mrg_left_key (MBth # p) = True # mrg_left_key p"

definition no_right :: "mrg list \<Rightarrow> bool" where
  "no_right p = list_all (\<lambda>m. m \<noteq> MRgt) p"

lemma no_right_mrg_plan:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow>
     no_right (mrg_plan cs1 cs2) = (set cs2 \<subseteq> set cs1)"
  by (induct cs1 cs2 rule: mrg_plan.induct) (auto simp: no_right_def list_all_iff)

lemma dproj_mrg_left_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     dproj (mrg_left_key (mrg_plan cs1 cs2)) (map f cs1) = map f cs2"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

text \<open>Reading the shared columns out of a short tuple is the same as taking the short form of
  the kernel's restriction.\<close>

lemma dproj_left_key_eq:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2" and sub: "set cs2 \<subseteq> set cs1"
  shows "dproj (mrg_left_key (mrg_plan cs1 cs2)) (restrict cs1 ks1 a)
       = restrict cs2 ks2 (restrict ks2 ks1 a)"
proof -
  have "set cs2 \<subseteq> set ks2" using f2 by (simp add: dframe_def)
  then show ?thesis
    using dproj_mrg_left_key[OF dframeD(2)[OF f1] dframeD(2)[OF f2] sub, of "tup_get ks1 a"]
    by (simp add: restrict_map[symmetric] restrict_restrict)
qed

subsection \<open>The join when one operand's columns are among the other's\<close>

definition dsemi :: "bool list \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "dsemi msk pos A B = Set.filter (\<lambda>a. (dproj msk a \<in> B) = pos) A"

lemma join_cond_eq: "join_cond pos t v = ((v \<in> t) = pos)"
  by (cases pos) auto

lemma join_sub_eq:
  assumes "distinct ks1" "distinct ks2" "table ks1 T" "table ks2 T'" "set ks2 \<subseteq> set ks1"
  shows "join ks1 T pos ks2 T' = {a \<in> T. (restrict ks2 ks1 a \<in> T') = pos}"
  using join_sub[OF assms] by (simp add: join_cond_eq)

text \<open>
  This is the shape the anti-join of @{text "\<phi> AND NOT \<psi>"} takes, and the intersection when the
  two column lists are equal: every tuple of the left operand either has a partner or does not,
  and the test is a membership of its projection.
\<close>

theorem dsemi_join:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2" and sub: "set cs2 \<subseteq> set cs1"
    and t1: "table ks1 T" and t2: "table ks2 T'"
  shows "dsemi (mrg_left_key (mrg_plan cs1 cs2)) pos (dtabc ks1 cs1 T) (dtabc ks2 cs2 T')
       = dtabc ks1 cs1 (join ks1 T pos ks2 T')"
proof -
  have subk: "set ks2 \<subseteq> set ks1" using f1 f2 sub by (simp add: dframe_def)
  have "join ks1 T pos ks2 T' = {a \<in> T. (restrict ks2 ks1 a \<in> T') = pos}"
    by (rule join_sub_eq[OF dframeD(1)[OF f1] dframeD(1)[OF f2] t1 t2 subk])
  moreover have "\<And>a. (dproj (mrg_left_key (mrg_plan cs1 cs2)) (restrict cs1 ks1 a)
      \<in> dtabc ks2 cs2 T') = (restrict ks2 ks1 a \<in> T')"
    unfolding dproj_left_key_eq[OF f1 f2 sub] by (rule dtabc_in_iff[OF f2 t2]) simp
  ultimately show ?thesis
    unfolding dsemi_def dtabc_def by auto
qed

subsection \<open>The short form of a table commutes with intersection, difference and union\<close>

lemma dtabc_Int:
  assumes f: "dframe ks cs" and t1: "table ks T" and t2: "table ks T'"
  shows "dtabc ks cs (T \<inter> T') = dtabc ks cs T \<inter> dtabc ks cs T'"
proof (intro equalityI subsetI)
  fix z assume "z \<in> dtabc ks cs T \<inter> dtabc ks cs T'"
  then obtain a a' where a: "a \<in> T" "a' \<in> T'" "z = restrict cs ks a" "z = restrict cs ks a'"
    by (auto simp: dtabc_def)
  then have "a = a'"
    using restrict_inv[OF f, of a] restrict_inv[OF f, of a'] t1 t2 by (auto simp: table_def)
  then show "z \<in> dtabc ks cs (T \<inter> T')" using a by (auto simp: dtabc_def)
qed (auto simp: dtabc_def)

subsection \<open>Equal columns, and a right operand with no columns\<close>

lemma mrg_plan_self: "mrg_plan cs cs = map (\<lambda>_. MBth) cs"
  by (induct cs) auto

lemma dproj_all_True: "dproj (mrg_left_key (map (\<lambda>_. MBth) cs)) xs = take (length cs) xs"
  by (induct cs arbitrary: xs; case_tac xs) auto

theorem dtabc_join_eq:
  assumes f1: "dframe ks1 cs" and f2: "dframe ks2 cs" and t1: "table ks1 T" and t2: "table ks2 T'"
  shows "(if pos then dtabc ks1 cs T \<inter> dtabc ks2 cs T' else dtabc ks1 cs T - dtabc ks2 cs T')
       = dtabc ks1 cs (join ks1 T pos ks2 T')"
proof -
  have p: "dproj (mrg_left_key (mrg_plan cs cs)) (restrict cs ks a) = restrict cs ks a"
    for ks and a :: "'a list"
    by (simp add: mrg_plan_self dproj_all_True)
  have "dsemi (mrg_left_key (mrg_plan cs cs)) pos (dtabc ks1 cs T) (dtabc ks2 cs T')
      = (if pos then dtabc ks1 cs T \<inter> dtabc ks2 cs T' else dtabc ks1 cs T - dtabc ks2 cs T')"
    unfolding dsemi_def by (auto simp: dtabc_def p)
  then show ?thesis
    using dsemi_join[OF f1 f2 subset_refl t1 t2, of pos] by simp
qed

lemma dtabc_Nil_cols:
  assumes "table [] T'"
  shows "dtabc [] [] T' = T'"
  using dtabc_same[of "[]" T'] assms by simp

theorem dtabc_join_no_cols:
  assumes f1: "dframe ks1 cs" and t1: "table ks1 T" and t2: "table [] T'"
  shows "(if pos = ([] \<in> dtabc [] [] T') then dtabc ks1 cs T else {})
       = dtabc ks1 cs (join ks1 T pos [] T')"
proof -
  have "join ks1 T pos [] T' = {a \<in> T. ([] \<in> T') = pos}"
    using join_sub_eq[of ks1 "[]" T T' pos] dframeD(1)[OF f1] t1 t2 by simp
  then show ?thesis using dtabc_Nil_cols[OF t2] by (auto simp: dtabc_def)
qed

subsection \<open>The join the other way round\<close>

fun mrg_right_key :: "mrg list \<Rightarrow> bool list" where
  "mrg_right_key [] = []"
| "mrg_right_key (MLft # p) = mrg_right_key p"
| "mrg_right_key (MRgt # p) = False # mrg_right_key p"
| "mrg_right_key (MBth # p) = True # mrg_right_key p"

definition no_left :: "mrg list \<Rightarrow> bool" where
  "no_left p = list_all (\<lambda>m. m \<noteq> MLft) p"

lemma no_left_mrg_plan:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow>
     no_left (mrg_plan cs1 cs2) = (set cs1 \<subseteq> set cs2)"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: no_left_def list_all_iff)
next
  case (3 c cs d ds)
  have s1: "sorted_wrt (<) cs" and hc: "\<forall>x \<in> set cs. c < x"
    and s2: "sorted_wrt (<) ds" and hd: "\<forall>x \<in> set ds. d < x"
    using 3(4,5) by auto
  consider (lt) "c < d" | (gt) "d < c" | (eq) "c = d" by force
  then show ?case
  proof cases
    case lt
    have "c \<notin> set (d # ds)" using lt hd by force
    then show ?thesis using lt by (simp add: no_left_def)
  next
    case gt
    have "d \<notin> set (c # cs)" using gt hc by force
    then have "(set (c # cs) \<subseteq> set (d # ds)) = (set (c # cs) \<subseteq> set ds)" by auto
    then show ?thesis using 3(2)[OF _ gt 3(4) s2] gt by (simp add: no_left_def)
  next
    case eq
    have "(set (c # cs) \<subseteq> set (d # ds)) = (set cs \<subseteq> set ds)" using eq hc by force
    then show ?thesis using 3(3)[OF _ _ s1 s2] eq by (simp add: no_left_def)
  qed
qed (simp add: no_left_def)

lemma dproj_replicate_False: "length xs = k \<Longrightarrow> dproj (replicate k False) xs = []"
  by (induct xs arbitrary: k) auto

lemma mrg_right_key_all_MRgt: "mrg_right_key (map (\<lambda>_. MRgt) ds) = replicate (length ds) False"
  by (induct ds) auto

lemma dproj_mrg_right_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs1 \<subseteq> set cs2 \<Longrightarrow>
     dproj (mrg_right_key (mrg_plan cs1 cs2)) (map g cs2) = map g cs1"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: mrg_right_key_all_MRgt dproj_replicate_False)
next
  case (3 c cs d ds)
  have s1: "sorted_wrt (<) cs" and hc: "\<forall>x \<in> set cs. c < x"
    and s2: "sorted_wrt (<) ds" and hd: "\<forall>x \<in> set ds. d < x"
    using 3(4,5) by auto
  consider (lt) "c < d" | (gt) "d < c" | (eq) "c = d" by force
  then show ?case
  proof cases
    case lt
    have "c \<notin> set (d # ds)" using lt hd by auto
    then show ?thesis using 3(6) by auto
  next
    case gt
    have "d \<notin> set (c # cs)" using gt hc by force
    then have "set (c # cs) \<subseteq> set ds" using 3(6) by auto
    then show ?thesis using 3(2)[OF _ gt 3(4) s2] gt by simp
  next
    case eq
    have "set cs \<subseteq> set ds" using 3(6) eq hc by force
    then show ?thesis using 3(3)[OF _ _ s1 s2] eq by simp
  qed
qed simp

lemma dproj_right_key_eq:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2" and sub: "set cs1 \<subseteq> set cs2"
  shows "dproj (mrg_right_key (mrg_plan cs1 cs2)) (restrict cs2 ks2 b)
       = restrict cs1 ks1 (restrict ks1 ks2 b)"
proof -
  have "set cs1 \<subseteq> set ks1" using f1 by (simp add: dframe_def)
  then show ?thesis
    using dproj_mrg_right_key[OF dframeD(2)[OF f1] dframeD(2)[OF f2] sub, of "tup_get ks2 b"]
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

theorem dsup_join:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2" and sub: "set cs1 \<subseteq> set cs2"
    and t1: "table ks1 T" and t2: "table ks2 T'"
  shows "Set.filter (\<lambda>b. dproj (mrg_right_key (mrg_plan cs1 cs2)) b \<in> dtabc ks1 cs1 T)
           (dtabc ks2 cs2 T')
       = dtabc (cols_union ks1 ks2) cs2 (join ks1 T True ks2 T')"
proof -
  let ?U = "cols_union ks1 ks2"
  have subk: "set ks1 \<subseteq> set ks2" using f1 f2 sub by (simp add: dframe_def)
  have j: "join ks1 T True ks2 T' = restrict ?U ks2 ` {b \<in> T'. restrict ks1 ks2 b \<in> T}"
    by (rule join_sub'[OF dframeD(1)[OF f1] dframeD(1)[OF f2] t1 t2 subk])
  have c2: "set cs2 \<subseteq> set ?U" using f2 by (auto simp: dframe_def)
  have mem: "\<And>b. (dproj (mrg_right_key (mrg_plan cs1 cs2)) (restrict cs2 ks2 b) \<in> dtabc ks1 cs1 T)
      = (restrict ks1 ks2 b \<in> T)"
    unfolding dproj_right_key_eq[OF f1 f2 sub] by (rule dtabc_in_iff[OF f1 t1]) simp
  have e: "\<And>x. restrict cs2 ?U (restrict ?U ks2 x) = restrict cs2 ks2 x"
    by (rule restrict_restrict[OF c2])
  show ?thesis
    unfolding j dtabc_def[of ks2 cs2] dtabc_def[of ?U cs2] image_image e
    using mem by auto
qed

text \<open>The general join's shapes need the right operand's columns among the left's for an
  antijoin; the result frame of a join is the merge of the two.\<close>

lemma dtabc_join_sub_res:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2" and sub: "set cs2 \<subseteq> set cs1"
  shows "cols_union ks1 ks2 = ks1" "merge_cols cs1 cs2 = cs1"
proof -
  show "cols_union ks1 ks2 = ks1"
    using f1 f2 sub by (intro cols_union_subset) (simp add: dframe_def)
  show "merge_cols cs1 cs2 = cs1"
    by (rule merge_cols_sub_left[OF dframeD(2)[OF f1] dframeD(2)[OF f2] sub])
qed

subsection \<open>The general join: an index on the shared columns\<close>

text \<open>
  When neither operand's columns are contained in the other's, one side is indexed by the
  shared columns and the other probes the index.  A probe that hits knows the two tuples agree
  on the shared columns, so the merge needs no test at all.
\<close>

fun dmerge :: "mrg list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "dmerge [] xs ys = []"
| "dmerge (MLft # p) (x # xs) ys = x # dmerge p xs ys"
| "dmerge (MRgt # p) xs (y # ys) = y # dmerge p xs ys"
| "dmerge (MBth # p) (x # xs) (y # ys) = x # dmerge p xs ys"
| "dmerge (m # p) xs ys = []"

lemma length_filter_mrg_plan_left: "length (filter (\<lambda>m. m \<noteq> MRgt) (mrg_plan cs1 cs2)) = length cs1"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

lemma length_filter_mrg_plan_right: "length (filter (\<lambda>m. m \<noteq> MLft) (mrg_plan cs1 cs2)) = length cs2"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

text \<open>The join of two short tuples succeeds exactly when they agree on the shared columns, and
  then it is the test-free merge.\<close>

lemma djoin1_dmerge:
  "length a = length (filter (\<lambda>m. m \<noteq> MRgt) p) \<Longrightarrow>
   length b = length (filter (\<lambda>m. m \<noteq> MLft) p) \<Longrightarrow>
   djoin1 p a b = (if dproj (mrg_left_key p) a = dproj (mrg_right_key p) b
                   then Some (dmerge p a b) else None)"
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

definition dindex_step :: "bool list \<Rightarrow> event_data tuple \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping" where
  "dindex_step msk b m = (let k = dproj msk b in
     (case Mapping.lookup m k of None \<Rightarrow> Mapping.update k [b] m
      | Some l \<Rightarrow> Mapping.update k (b # l) m))"

definition dindex :: "bool list \<Rightarrow> event_data table \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping" where
  "dindex msk B = fold (dindex_step msk) (csl B) Mapping.empty"

definition dprobe_step :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping \<Rightarrow> event_data tuple \<Rightarrow>
    event_data table \<Rightarrow> event_data table" where
  "dprobe_step p msk m a acc = (case Mapping.lookup m (dproj msk a) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>b acc. Set.insert (dmerge p a b) acc) l acc)"

definition dprobe_step_l :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping \<Rightarrow> event_data tuple \<Rightarrow>
    event_data table \<Rightarrow> event_data table" where
  "dprobe_step_l p rk m y acc = (case Mapping.lookup m (dproj rk y) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>x acc. Set.insert (dmerge p x y) acc) l acc)"

text \<open>The index is built on the smaller side and the larger one probes it: indexing costs a
  lookup per tuple of the indexed side and probing one per tuple of the other, so indexing the
  larger side buys a big index that is read a few times.\<close>

definition dgen_join :: "mrg list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
    event_data table \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dgen_join p lk rk A B =
     (if card A \<le> card B
      then (let m = dindex lk A in fold (dprobe_step_l p rk m) (csl B) empty_table)
      else (let m = dindex rk B in fold (dprobe_step p lk m) (csl A) empty_table))"

definition bucket :: "(event_data tuple, event_data tuple list) mapping \<Rightarrow>
    event_data tuple \<Rightarrow> event_data tuple list" where
  "bucket m k = (case Mapping.lookup m k of None \<Rightarrow> [] | Some l \<Rightarrow> l)"

lemma fold_insert_image: "fold (\<lambda>b acc. Set.insert (f b) acc) l acc = f ` set l \<union> acc"
  by (induct l arbitrary: acc) auto

lemma bucket_dindex_step:
  "bucket (dindex_step msk x m) k = (if dproj msk x = k then x # bucket m k else bucket m k)"
  by (auto simp: bucket_def dindex_step_def Let_def Mapping.lookup_update'
      split: option.splits)

lemma dindex_fold_lookup:
  "set (bucket (fold (dindex_step msk) xs m) k)
   = {b \<in> set xs. dproj msk b = k} \<union> set (bucket m k)"
  by (induct xs arbitrary: m) (auto simp: bucket_dindex_step)

lemma dindex_lookup:
  assumes "set (csl B) = B"
  shows "set (bucket (dindex msk B) k) = {b \<in> B. dproj msk b = k}"
  using dindex_fold_lookup[of msk "csl B" Mapping.empty k] assms
  by (simp add: dindex_def bucket_def)

lemma dprobe_fold:
  "fold (dprobe_step p lk m) xs acc
   = acc \<union> (\<Union>a \<in> set xs. (\<lambda>b. dmerge p a b) ` set (bucket m (dproj lk a)))"
  by (induct xs arbitrary: acc)
    (auto simp: dprobe_step_def bucket_def fold_insert_image split: option.splits)

lemma dprobe_l_fold:
  "fold (dprobe_step_l p rk m) ys acc
   = acc \<union> (\<Union>y \<in> set ys. (\<lambda>x. dmerge p x y) ` set (bucket m (dproj rk y)))"
  by (induct ys arbitrary: acc)
    (auto simp: dprobe_step_l_def bucket_def fold_insert_image split: option.splits)

text \<open>Both sides of the size test compute the same table: the pairs that agree on the shared
  columns, merged.\<close>

lemma dgen_join_eq:
  assumes cA: "set (csl A) = A" and cB: "set (csl B) = B"
  shows "dgen_join p lk rk A B
       = {dmerge p a b | a b. a \<in> A \<and> b \<in> B \<and> dproj lk a = dproj rk b}"
  by (auto simp: dgen_join_def Let_def dprobe_fold dprobe_l_fold empty_table_def
      dindex_lookup[OF cA] dindex_lookup[OF cB] cA cB) force

lemma set_option_djoin1:
  "length a = length (filter (\<lambda>m. m \<noteq> MRgt) p) \<Longrightarrow>
   length b = length (filter (\<lambda>m. m \<noteq> MLft) p) \<Longrightarrow>
   set_option (djoin1 p a b)
     = (if dproj (mrg_left_key p) a = dproj (mrg_right_key p) b then {dmerge p a b} else {})"
  by (simp add: djoin1_dmerge)

lemma set_csl_dtabc:
  "finite T \<Longrightarrow> set (csl (dtabc ks cs (T :: event_data table))) = dtabc ks cs T"
  by (simp add: csl_finite finite_dtabc set_csorted_list_of_set_etuple)

theorem dtabc_gen_join:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2"
    and t1: "table ks1 T" and t2: "table ks2 T'"
    and fT: "finite T" and fT': "finite T'"
  shows "dgen_join (mrg_plan cs1 cs2) (mrg_left_key (mrg_plan cs1 cs2))
           (mrg_right_key (mrg_plan cs1 cs2)) (dtabc ks1 cs1 T) (dtabc ks2 cs2 T')
       = dtabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T True ks2 T')"
proof -
  let ?p = "mrg_plan cs1 cs2"
  have la: "\<And>a. a \<in> dtabc ks1 cs1 T \<Longrightarrow> length a = length (filter (\<lambda>m. m \<noteq> MRgt) ?p)"
    by (auto simp: dtabc_def length_filter_mrg_plan_left)
  have lb: "\<And>b. b \<in> dtabc ks2 cs2 T' \<Longrightarrow> length b = length (filter (\<lambda>m. m \<noteq> MLft) ?p)"
    by (auto simp: dtabc_def length_filter_mrg_plan_right)
  have "dgen_join ?p (mrg_left_key ?p) (mrg_right_key ?p) (dtabc ks1 cs1 T) (dtabc ks2 cs2 T')
      = (\<Union>a \<in> dtabc ks1 cs1 T. \<Union>b \<in> dtabc ks2 cs2 T'. set_option (djoin1 ?p a b))"
    unfolding dgen_join_eq[OF set_csl_dtabc[OF fT] set_csl_dtabc[OF fT']]
    by (auto simp: set_option_djoin1[OF la lb] split: if_splits)
  also have "\<dots> = dtabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T True ks2 T')"
    by (rule dtabc_join[OF f1 f2 t1, symmetric])
  finally show ?thesis .
qed

subsection \<open>Dispatching on the shape of the two column lists\<close>

text \<open>
  The plan is computed once, when the formula is compiled, and replayed at every time point;
  the kernel's @{const bin_join} recomputes the same case distinction from the two column lists
  on every call.
\<close>

datatype djoin_plan =
    DJEq | DJEmp | DJSub "bool list" | DJSup "bool list"
  | DJGen "mrg list" "bool list" "bool list"

definition mk_djoin :: "cols \<Rightarrow> cols \<Rightarrow> djoin_plan" where
  "mk_djoin cs1 cs2 = (if cs1 = cs2 then DJEq else if cs2 = [] then DJEmp
     else (let p = mrg_plan cs1 cs2 in
       if no_right p then DJSub (mrg_left_key p)
       else if no_left p then DJSup (mrg_right_key p)
       else DJGen p (mrg_left_key p) (mrg_right_key p)))"

fun dbin_join0 :: "djoin_plan \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> event_data table \<Rightarrow>
    event_data table" where
  "dbin_join0 DJEq A pos B = (if pos then A \<inter> B else A - B)"
| "dbin_join0 DJEmp A pos B = (if pos = ([] \<in> B) then A else empty_table)"
| "dbin_join0 (DJSub msk) A pos B = dsemi msk pos A B"
| "dbin_join0 (DJSup msk) A pos B = (if pos then Set.filter (\<lambda>b. dproj msk b \<in> A) B else A)"
| "dbin_join0 (DJGen p lk rk) A pos B = (if pos then dgen_join p lk rk A B else A)"

definition dbin_join :: "djoin_plan \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> event_data table \<Rightarrow>
    event_data table" where
  "dbin_join pl A pos B = (if Set.is_empty A then empty_table
     else if Set.is_empty B then (if pos then empty_table else A)
     else dbin_join0 pl A pos B)"

text \<open>Every shape of the plan computes the short form of the kernel's join.  A negative join
  needs the right operand's columns among the left's, which is what the safety condition of
  @{text "\<phi> AND NOT \<psi>"} provides; the other shapes then arise only for a positive join.\<close>

theorem dbin_join0_join:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2"
    and t1: "table ks1 T" and t2: "table ks2 T'"
    and neg: "\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1"
    and fT: "finite T" and fT': "finite T'"
  shows "dbin_join0 (mk_djoin cs1 cs2) (dtabc ks1 cs1 T) pos (dtabc ks2 cs2 T')
       = dtabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T pos ks2 T')"
proof (cases "cs1 = cs2")
  case True
  then have f2': "dframe ks2 cs1" using f2 by simp
  have sub: "set cs2 \<subseteq> set cs1" using True by simp
  have "dbin_join0 (mk_djoin cs1 cs2) (dtabc ks1 cs1 T) pos (dtabc ks2 cs2 T')
      = (if pos then dtabc ks1 cs1 T \<inter> dtabc ks2 cs1 T' else dtabc ks1 cs1 T - dtabc ks2 cs1 T')"
    using True by (simp add: mk_djoin_def)
  also have "\<dots> = dtabc ks1 cs1 (join ks1 T pos ks2 T')"
    by (rule dtabc_join_eq[OF f1 f2' t1 t2])
  finally show ?thesis using dtabc_join_sub_res[OF f1 f2 sub] by simp
next
  case ne: False
  note s1 = dframeD(2)[OF f1] and s2 = dframeD(2)[OF f2]
  show ?thesis
  proof (cases "cs2 = []")
    case True
    then have k2: "ks2 = []" using f2 by (simp add: dframe_def)
    then have tt: "table [] T'" using t2 by simp
    have "dbin_join0 (mk_djoin cs1 cs2) (dtabc ks1 cs1 T) pos (dtabc ks2 cs2 T')
        = (if pos = ([] \<in> dtabc [] [] T') then dtabc ks1 cs1 T else {})"
      using ne True k2 by (simp add: mk_djoin_def empty_table_def)
    also have "\<dots> = dtabc ks1 cs1 (join ks1 T pos [] T')" by (rule dtabc_join_no_cols[OF f1 t1 tt])
    finally show ?thesis using True k2 by (simp add: merge_cols_Nil2)
  next
    case ne2: False
    let ?p = "mrg_plan cs1 cs2"
    show ?thesis
    proof (cases "no_right ?p")
      case True
      then have sub: "set cs2 \<subseteq> set cs1" using no_right_mrg_plan[OF s1 s2] by simp
      show ?thesis using dsemi_join[OF f1 f2 sub t1 t2, of pos]
          dtabc_join_sub_res[OF f1 f2 sub] ne ne2 True
        by (simp add: mk_djoin_def)
    next
      case nr: False
      then have nsub: "\<not> set cs2 \<subseteq> set cs1" using no_right_mrg_plan[OF s1 s2] by simp
      then have p: "pos" using neg by blast
      show ?thesis
      proof (cases "no_left ?p")
        case True
        then have sub: "set cs1 \<subseteq> set cs2" using no_left_mrg_plan[OF s1 s2] by simp
        show ?thesis using dsup_join[OF f1 f2 sub t1 t2]
            merge_cols_sub_right[OF s1 s2 sub] ne ne2 nr True p
          by (simp add: mk_djoin_def)
      next
        case False
        show ?thesis using dtabc_gen_join[OF f1 f2 t1 t2 fT fT'] ne ne2 nr False p
          by (simp add: mk_djoin_def Let_def)
      qed
    qed
  qed
qed

theorem dbin_join_join:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2"
    and t1: "table ks1 T" and t2: "table ks2 T'"
    and neg: "\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1"
    and fT: "finite T" and fT': "finite T'"
  shows "dbin_join (mk_djoin cs1 cs2) (dtabc ks1 cs1 T) pos (dtabc ks2 cs2 T')
       = dtabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (join ks1 T pos ks2 T')"
proof (cases "T = {}")
  case True
  then show ?thesis
    by (cases pos) (simp_all add: dbin_join_def dtabc_empty_iff join_False_code empty_table_def)
next
  case T: False
  show ?thesis
  proof (cases "T' = {}")
    case True
    show ?thesis
    proof (cases pos)
      case False
      then have sub: "set cs2 \<subseteq> set cs1" by (rule neg)
      show ?thesis using T True False dtabc_join_sub_res[OF f1 f2 sub]
        by (simp add: dbin_join_def dtabc_empty_iff join_False_code empty_table_def)
    qed (use T True in \<open>simp add: dbin_join_def dtabc_empty_iff empty_table_def\<close>)
  next
    case False
    then show ?thesis using T
      by (simp add: dbin_join_def dtabc_empty_iff dbin_join0_join[OF f1 f2 t1 t2 neg fT fT'])
  qed
qed

text \<open>And hence the short join refines the kernel's @{const bin_join}.\<close>

subsection \<open>The multi-way join\<close>

text \<open>
  The kernel's @{const mmulti_join} picks a strategy at run time; the dense evaluator joins left
  to right against a plan list computed once.  Both compute the tuples over the union of the
  positive operands' columns that restrict into every positive operand and into no negative
  one, which the left-to-right folds below are shown to compute as well.
\<close>

fun dands_plans :: "cols \<Rightarrow> cols list \<Rightarrow> djoin_plan list" where
  "dands_plans acc [] = []"
| "dands_plans acc (c # cs) = mk_djoin acc c # dands_plans (merge_cols acc c) cs"

fun dands_cols :: "cols \<Rightarrow> cols list \<Rightarrow> cols" where
  "dands_cols acc [] = acc"
| "dands_cols acc (c # cs) = dands_cols (merge_cols acc c) cs"

fun dands_pos :: "djoin_plan list \<Rightarrow> event_data table \<Rightarrow> event_data table list \<Rightarrow>
    event_data table" where
  "dands_pos [] t us = t"
| "dands_pos (p # ps) t [] = t"
| "dands_pos (p # ps) t (u # us) = dands_pos ps (dbin_join p t True u) us"

fun dands_neg :: "djoin_plan list \<Rightarrow> event_data table \<Rightarrow> event_data table list \<Rightarrow>
    event_data table" where
  "dands_neg [] t us = t"
| "dands_neg (p # ps) t [] = t"
| "dands_neg (p # ps) t (u # us) = dands_neg ps (dbin_join p t False u) us"

text \<open>The kernel's tables of the same folds, over the kernel's column orders.\<close>

fun kands_cols :: "cols \<Rightarrow> cols list \<Rightarrow> cols" where
  "kands_cols acc [] = acc"
| "kands_cols acc (k # ks) = kands_cols (cols_union acc k) ks"

fun kands_pos :: "cols \<Rightarrow> 'a table \<Rightarrow> (cols \<times> 'a table) list \<Rightarrow> 'a table" where
  "kands_pos acc t [] = t"
| "kands_pos acc t ((k, u) # us) = kands_pos (cols_union acc k) (join acc t True k u) us"

fun kands_neg :: "cols \<Rightarrow> 'a table \<Rightarrow> (cols \<times> 'a table) list \<Rightarrow> 'a table" where
  "kands_neg acc t [] = t"
| "kands_neg acc t ((k, u) # us) = kands_neg acc (join acc t False k u) us"

lemma finite_join: "finite X \<Longrightarrow> finite Y \<Longrightarrow> finite (join cs X b ds Y)"
  by (cases b) (auto simp: join_True_code join_False_code)

lemma set_kands_cols: "set (kands_cols acc kss) = set acc \<union> (\<Union>k \<in> set kss. set k)"
  by (induct kss arbitrary: acc) auto

lemma distinct_kands_cols:
  "distinct acc \<Longrightarrow> \<forall>k \<in> set kss. distinct k \<Longrightarrow> distinct (kands_cols acc kss)"
  by (induct kss arbitrary: acc) auto

lemma dframe_dands_cols:
  assumes "list_all2 dframe kss css" and "dframe acc c"
  shows "dframe (kands_cols acc kss) (dands_cols c css)"
  using assms
proof (induct kss css arbitrary: acc c rule: list_all2_induct)
  case (Cons k ks c' cs)
  show ?case using Cons(3)[OF dframe_merge[OF Cons(4) Cons(1)]] by simp
qed simp

text \<open>An operand of the multi-way join: its kernel columns, its dense columns, and its table.\<close>

definition wf_operand :: "cols \<Rightarrow> cols \<Rightarrow> event_data table \<Rightarrow> bool" where
  "wf_operand k c U \<longleftrightarrow> dframe k c \<and> table k U \<and> finite U"

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
  have dk: "distinct k" "table k u" using Cons(4) ku by auto
  have tj: "table ?U (join acc t True k u)"
    using Cons(3) dk by (intro join_table) auto
  have sub: "set ?U \<subseteq> set ?K" by (simp add: set_kands_cols)
  have IH: "z \<in> kands_pos ?U (join acc t True k u) us \<longleftrightarrow> wf_tuple ?K z \<and>
      restrict ?U ?K z \<in> join acc t True k u \<and> (\<forall>(k, u) \<in> set us. restrict k ?K z \<in> u)"
    using Cons(1)[of ?U "join acc t True k u"] Cons(2,4) dk tj by auto
  have j: "restrict ?U ?K z \<in> join acc t True k u \<longleftrightarrow>
      restrict acc ?K z \<in> t \<and> restrict k ?K z \<in> u"
    using join_restrict[OF Cons(2) dk(1) Cons(3) dk(2), of True "restrict ?U ?K z"]
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
  have dk: "distinct k" "table k u" "set k \<subseteq> set acc" using Cons(4) ku by auto
  have j: "join acc t False k u = {a \<in> t. restrict k acc a \<notin> u}"
    using join_sub_eq[OF Cons(2) dk(1) Cons(3) dk(2,3), of False] by simp
  have tj: "table acc (join acc t False k u)"
    using Cons(3) by (auto simp: j table_def)
  show ?case using Cons(1)[OF Cons(2) tj] Cons(4) by (auto simp: ku j)
qed simp

theorem dands_pos_dtabc:
  assumes "dframe acc c" and "table acc T" and "finite T"
    and "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Us"
  shows "dands_pos (dands_plans c (map snd kcs)) (dtabc acc c T) (map2 (\<lambda>(k, c). dtabc k c) kcs Us)
       = dtabc (kands_cols acc (map fst kcs)) (dands_cols c (map snd kcs)) (kands_pos acc T (zip (map fst kcs) Us))"
  using assms
proof (induct kcs arbitrary: acc c T Us)
  case (Cons kc kcs)
  obtain k c' where kc: "kc = (k, c')" by (cases kc)
  from Cons(5) obtain U Us' where U: "Us = U # Us'" and wf: "wf_operand k c' U"
    and rest: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Us'"
    by (cases Us) (auto simp: kc)
  have f': "dframe k c'" and tU: "table k U" and fU: "finite U" using wf by (auto simp: wf_operand_def)
  have j: "dbin_join (mk_djoin c c') (dtabc acc c T) True (dtabc k c' U)
      = dtabc (cols_union acc k) (merge_cols c c') (join acc T True k U)"
    by (rule dbin_join_join[OF Cons(2) f' Cons(3) tU _ Cons(4) fU]) simp
  have t: "table (cols_union acc k) (join acc T True k U)"
    using Cons(3) tU by (intro join_table) auto
  show ?case
    unfolding U kc using Cons(1)[OF dframe_merge[OF Cons(2) f'] t finite_join[OF Cons(4) fU] rest]
    by (simp add: j)
qed simp

theorem dands_neg_dtabc:
  assumes "dframe acc c" and "table acc T" and "finite T"
    and "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Vs" and "\<forall>c' \<in> set (map snd kcs). set c' \<subseteq> set c"
  shows "dands_neg (dands_plans c (map snd kcs)) (dtabc acc c T) (map2 (\<lambda>(k, c). dtabc k c) kcs Vs)
       = dtabc acc c (kands_neg acc T (zip (map fst kcs) Vs))"
  using assms
proof (induct kcs arbitrary: T Vs)
  case (Cons kc kcs)
  obtain k c' where kc: "kc = (k, c')" by (cases kc)
  from Cons(5) obtain V Vs' where V: "Vs = V # Vs'" and wf: "wf_operand k c' V"
    and rest: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Vs'"
    by (cases Vs) (auto simp: kc)
  have f': "dframe k c'" and tV: "table k V" and fV: "finite V" using wf by (auto simp: wf_operand_def)
  have sub: "set c' \<subseteq> set c" using Cons(6) kc by simp
  note res = dtabc_join_sub_res[OF Cons(2) f' sub]
  have j: "dbin_join (mk_djoin c c') (dtabc acc c T) False (dtabc k c' V)
      = dtabc acc c (join acc T False k V)"
    using dbin_join_join[OF Cons(2) f' Cons(3) tV _ Cons(4) fV, of False] sub res by simp
  have t: "table acc (join acc T False k V)"
    using Cons(3) tV sub Cons(2) f' by (intro join_table) (auto simp: dframe_def res)
  show ?case
    unfolding V kc
    using Cons(1)[OF Cons(2) t finite_join[OF Cons(4) fV] rest] Cons(6) res
    by (simp add: j)
qed simp

text \<open>The kernel's multi-way join is the left-to-right fold, read in its own column order.\<close>

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

section \<open>Aggregation over short tuples\<close>

subsection \<open>Reading a term at the short tuple's positions\<close>

fun col_pos :: "cols \<Rightarrow> nat \<Rightarrow> nat" where
  "col_pos [] x = 0"
| "col_pos (c # cs) x = (if c = x then 0 else Suc (col_pos cs x))"

fun reindex_trm :: "cols \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" where
  "reindex_trm cs (Formula.Var x) = Formula.Var (col_pos cs x)"
| "reindex_trm cs (Formula.Const c) = Formula.Const c"
| "reindex_trm cs (Formula.Plus a b) = Formula.Plus (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.Minus a b) = Formula.Minus (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.UMinus a) = Formula.UMinus (reindex_trm cs a)"
| "reindex_trm cs (Formula.Mult a b) = Formula.Mult (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.Div a b) = Formula.Div (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.Mod a b) = Formula.Mod (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.F2i a) = Formula.F2i (reindex_trm cs a)"
| "reindex_trm cs (Formula.I2f a) = Formula.I2f (reindex_trm cs a)"

lemma col_pos_nth: "c \<in> set cs \<Longrightarrow> map f cs ! col_pos cs c = f c"
  by (induct cs) auto

lemma col_pos_length: "c \<in> set cs \<Longrightarrow> col_pos cs c < length cs"
  by (induct cs) auto

lemma fv_reindex_trm:
  "Formula.fv_trm t \<subseteq> set cs \<Longrightarrow> Formula.fv_trm (reindex_trm cs t) \<subseteq> {0..<length cs}"
  by (induct t) (auto simp: col_pos_length)

text \<open>The re-indexed term read at the dense tuple's positions is the original term read at the
  kernel's.\<close>

lemma umeval_trm_reindex:
  "Formula.fv_trm t \<subseteq> set cs' \<Longrightarrow> umeval_trm (reindex_trm cs' t) (restrict cs' cs x) = meval_trm cs t x"
  by (induct t) (auto simp: restrict_map col_pos_nth)

subsection \<open>The group key is a suffix of the dense tuple\<close>

text \<open>
  The aggregation's bound variables occupy the bottom of the frame and are contained in the
  operand's free variables, so the operand's dense column list is @{term "[0..<m]"} followed by
  the group's columns shifted up by @{term m}.  Under that decomposition the group key -- which
  the kernel reads off its own tuple with @{const agg_key}, over @{term "shift_cols m cs"} --
  is @{term "drop m"} of the dense tuple, over the group's columns.
\<close>

abbreviation agg_cols :: "nat \<Rightarrow> cols \<Rightarrow> cols" where
  "agg_cols m gcols \<equiv> [0..<m] @ map (\<lambda>c. c + m) gcols"

lemma agg_cols_sortedD: "sorted_wrt (<) (agg_cols m gcols) \<Longrightarrow> sorted_wrt (<) gcols"
  by (auto simp: sorted_wrt_append sorted_wrt_map)

lemma set_shift_agg_cols:
  "set cs = set (agg_cols m gcols) \<Longrightarrow> set (shift_cols m cs) = set gcols"
  by (force simp: set_shift_cols image_iff)

lemma dframe_shift_cols:
  assumes "dframe cs (agg_cols m gcols)"
  shows "dframe (shift_cols m cs) gcols"
  using dframeD(1,2)[OF assms] set_shift_agg_cols[OF dframeD(3)[OF assms, symmetric]]
  unfolding dframe_def by (simp add: distinct_shift_cols agg_cols_sortedD)

lemma tup_get_agg_key_shift:
  assumes "c \<in> set cs" "k \<le> c"
  shows "tup_get (shift_cols k cs) (agg_key k cs x) (c - k) = tup_get cs x c"
proof -
  have "tup_get (shift_cols k cs) (agg_key k cs x) (c - k) =
      tup_get (filter (\<lambda>x. k \<le> x) cs) (agg_key k cs x) c"
    unfolding shift_cols_def using assms by (intro tup_get_map) (auto simp: inj_on_def)
  also have "\<dots> = tup_get cs x c"
    unfolding agg_key_def using assms by (simp add: tup_get_restrict)
  finally show ?thesis .
qed

lemma wf_tuple_agg_key_shift: "wf_tuple (shift_cols k cs) (agg_key k cs x)"
  by (simp add: agg_key_def shift_cols_def wf_tuple_def)

lemma drop_restrict_agg:
  assumes "set (agg_cols m gcols) \<subseteq> set cs"
  shows "drop m (restrict (agg_cols m gcols) cs x) = restrict gcols (shift_cols m cs) (agg_key m cs x)"
proof -
  have "drop m (restrict (agg_cols m gcols) cs x) = map (\<lambda>c. tup_get cs x (c + m)) gcols"
    by (simp add: restrict_map)
  also have "\<dots> = restrict gcols (shift_cols m cs) (agg_key m cs x)"
    unfolding restrict_map
  proof (rule map_cong[OF refl])
    fix c assume "c \<in> set gcols"
    then have "c + m \<in> set cs" using assms by auto
    then show "tup_get cs x (c + m) = tup_get (shift_cols m cs) (agg_key m cs x) c"
      using tup_get_agg_key_shift[of "c + m" cs m x] by simp
  qed
  finally show ?thesis .
qed

subsection \<open>Writing the aggregate into the group key\<close>

definition ins_pos :: "cols \<Rightarrow> nat \<Rightarrow> nat" where
  "ins_pos cs y = length (filter (\<lambda>c. c < y) cs)"

lemma merge_cols_single:
  "sorted_wrt (<) cs \<Longrightarrow> y \<notin> set cs \<Longrightarrow>
     merge_cols cs [y] = take (ins_pos cs y) cs @ y # drop (ins_pos cs y) cs"
proof (induct cs)
  case (Cons c cs)
  show ?case
  proof (cases "c < y")
    case True
    then show ?thesis using Cons by (simp add: ins_pos_def)
  next
    case False
    then have yc: "y < c" using Cons(3) by auto
    then have "filter (\<lambda>d. d < y) (c # cs) = []" using Cons(2)
      by (force simp: filter_empty_conv)
    then show ?thesis using yc False by (simp add: ins_pos_def merge_cols_Nil2)
  qed
qed (simp add: ins_pos_def)

text \<open>The kernel puts the aggregate in front of the group key; the dense tuple has it at the
  one position @{term y} occupies among the group's columns.\<close>

lemma restrict_merge_single:
  assumes s: "sorted_wrt (<) gcols" and yg: "y \<notin> set gcols"
  shows "restrict (merge_cols gcols [y]) (y # ks) (v # k)
       = take (ins_pos gcols y) (restrict gcols ks k) @ v # drop (ins_pos gcols y) (restrict gcols ks k)"
proof -
  let ?p = "ins_pos gcols y"
  have upd: "tup_get (y # ks) (v # k) c = tup_get ks k c" if "c \<in> set gcols" for c
    using that yg by (auto simp: tup_get_Cons)
  have "restrict (merge_cols gcols [y]) (y # ks) (v # k)
      = map (tup_get (y # ks) (v # k)) (take ?p gcols @ y # drop ?p gcols)"
    by (simp add: restrict_map merge_cols_single[OF s yg])
  also have "\<dots> = map (tup_get ks k) (take ?p gcols) @ v # map (tup_get ks k) (drop ?p gcols)"
  proof -
    have t: "map (tup_get (y # ks) (v # k)) (take ?p gcols) = map (tup_get ks k) (take ?p gcols)"
      by (rule map_cong[OF refl]) (auto dest: in_set_takeD intro!: upd)
    have d: "map (tup_get (y # ks) (v # k)) (drop ?p gcols) = map (tup_get ks k) (drop ?p gcols)"
      by (rule map_cong[OF refl]) (auto dest: in_set_dropD intro!: upd)
    show ?thesis using t d by (simp add: tup_get_Cons)
  qed
  also have "\<dots> = take ?p (restrict gcols ks k) @ v # drop ?p (restrict gcols ks k)"
    by (simp add: restrict_map take_map drop_map)
  finally show ?thesis .
qed

subsection \<open>Selecting a group commutes with the reordering\<close>

lemma drop_restrict_agg_eq_iff:
  assumes f: "dframe cs (agg_cols m gcols)"
  shows "(drop m (restrict (agg_cols m gcols) cs x) = drop m (restrict (agg_cols m gcols) cs x'))
       = (agg_key m cs x = agg_key m cs x')"
proof -
  have sub: "set (agg_cols m gcols) \<subseteq> set cs" using dframeD(3)[OF f] by simp
  note i = inj_on_restrict[OF dframe_shift_cols[OF f]]
  show ?thesis
    unfolding drop_restrict_agg[OF sub]
  proof
    assume "restrict gcols (shift_cols m cs) (agg_key m cs x) = restrict gcols (shift_cols m cs) (agg_key m cs x')"
    then show "agg_key m cs x = agg_key m cs x'"
      by (rule inj_onD[OF i]) (simp_all add: wf_tuple_agg_key_shift)
  qed simp
qed

lemma dtabc_agg_group:
  assumes f: "dframe cs (agg_cols m gcols)"
  shows "Set.filter (\<lambda>z. drop m z = drop m (restrict (agg_cols m gcols) cs x0))
           (dtabc cs (agg_cols m gcols) rel)
       = dtabc cs (agg_cols m gcols) (Set.filter (\<lambda>x. agg_key m cs x = agg_key m cs x0) rel)"
  unfolding dtabc_def using drop_restrict_agg_eq_iff[OF f] by auto

subsection \<open>The aggregated values do not change\<close>

lemma uagg_values_dtabc:
  assumes f: "dframe cs (agg_cols m gcols)" and tG: "table cs G"
    and fv: "Formula.fv_trm f \<subseteq> set cs"
  shows "uagg_values (reindex_trm (agg_cols m gcols) f) (dtabc cs (agg_cols m gcols) G)
       = (\<lambda>v. (v, ecard (Set.filter (\<lambda>x. meval_trm cs f x = v) G))) ` meval_trm cs f ` G"
proof -
  let ?cc = "agg_cols m gcols"
  let ?r = "restrict ?cc cs"
  let ?g = "reindex_trm ?cc f"
  have ev: "umeval_trm ?g (?r x) = meval_trm cs f x" for x
    using fv dframeD(3)[OF f] by (intro umeval_trm_reindex) simp
  have inj: "inj_on ?r G"
    by (rule inj_on_subset[OF inj_on_restrict[OF f]]) (use tG in \<open>auto simp: table_def\<close>)
  have img: "umeval_trm ?g ` ?r ` G = meval_trm cs f ` G"
    unfolding image_image by (intro image_cong[OF refl] ev)
  show ?thesis
    unfolding uagg_values dtabc_def img
  proof (intro image_cong[OF refl])
    fix v :: event_data
    have fil: "Set.filter (\<lambda>z. umeval_trm ?g z = v) (?r ` G) = ?r ` Set.filter (\<lambda>x. meval_trm cs f x = v) G"
      by (auto simp: ev)
    have inj': "inj_on ?r (Set.filter (\<lambda>x. meval_trm cs f x = v) G)"
      by (rule inj_on_subset[OF inj]) auto
    show "(v, ecard (Set.filter (\<lambda>z. umeval_trm ?g z = v) (?r ` G)))
        = (v, ecard (Set.filter (\<lambda>x. meval_trm cs f x = v) G))"
      unfolding fil ecard_image[OF inj'] by (rule refl)
  qed
qed

subsection \<open>Aggregation over dense tuples agrees with the kernel's\<close>

text \<open>
  The dense aggregation takes the group key as a suffix of the dense tuple (of length
  @{term "length tys"} before it), and writes the aggregate at the position @{term y} occupies
  among the group's columns.  The kernel's result is over @{term "y # shift_cols (length tys) cs"},
  the dense one over the same columns in ascending order.
\<close>

theorem uagg_eval_agg:
  assumes f: "dframe cs (agg_cols (length tys) gcols)" and t: "table cs rel"
    and fv: "Formula.fv_trm f \<subseteq> set cs" and yg: "y \<notin> set gcols"
    and g0: "g0 \<Longrightarrow> gcols = []"
  shows "uagg g0 \<omega> (reindex_trm (agg_cols (length tys) gcols) f) (length tys) (ins_pos gcols y)
           (dtabc cs (agg_cols (length tys) gcols) rel)
       = dtabc (y # shift_cols (length tys) cs) (merge_cols gcols [y]) (eval_agg cs g0 \<omega> tys f rel)"
proof -
  let ?m = "length tys"
  let ?cc = "agg_cols ?m gcols"
  let ?r = "restrict ?cc cs"
  let ?S = "shift_cols ?m cs"
  let ?g = "reindex_trm ?cc f"
  let ?p = "ins_pos gcols y"
  let ?A = "\<lambda>x. eval_agg_op \<omega> ((\<lambda>x''. (meval_trm cs f x'', ecard (Set.filter
      (\<lambda>x'. meval_trm cs f x' = meval_trm cs f x'')
      (Set.filter (\<lambda>x'. agg_key ?m cs x' = agg_key ?m cs x) rel)))) `
      Set.filter (\<lambda>x'. agg_key ?m cs x' = agg_key ?m cs x) rel)"
  have sg: "sorted_wrt (<) gcols" using dframeD(2)[OF f] by (rule agg_cols_sortedD)
  have sub: "set ?cc \<subseteq> set cs" using dframeD(3)[OF f] by simp
  show ?thesis
  proof (cases "g0 \<and> rel = empty_table")
    case True
    then have e: "rel = {}" and g: "g0" by (auto simp: empty_table_def)
    have mc: "merge_cols gcols [y] = [y]" using g0[OF g] by simp
    show ?thesis
      using True e g by (simp add: uagg_def eval_agg_def dtabc_def singleton_table_def mc
          restrict_map tup_get_Cons empty_table_def)
  next
    case False
    then have ne: "\<not> (g0 \<and> Set.is_empty (?r ` rel))"
      by (auto simp: empty_table_def)
    have "uagg g0 \<omega> ?g ?m ?p (dtabc cs ?cc rel)
        = (\<lambda>k. take ?p k @ eval_agg_op \<omega>
          (uagg_values ?g (Set.filter (\<lambda>z. drop ?m z = k) (?r ` rel))) # drop ?p k)
          ` (drop ?m ` ?r ` rel)"
      unfolding uagg_def dtabc_def Let_def keys_cluster using ne
      by (auto simp: lookup_cluster_Some intro!: image_cong)
    also have "\<dots> = (\<lambda>x. restrict (merge_cols gcols [y]) (y # ?S) (?A x # agg_key ?m cs x)) ` rel"
      unfolding image_image
    proof (intro image_cong[OF refl])
      fix x assume x: "x \<in> rel"
      let ?gr = "Set.filter (\<lambda>x'. agg_key ?m cs x' = agg_key ?m cs x) rel"
      have k: "drop ?m (?r x) = restrict gcols ?S (agg_key ?m cs x)"
        by (rule drop_restrict_agg[OF sub])
      have grp: "Set.filter (\<lambda>z. drop ?m z = drop ?m (?r x)) (?r ` rel) = ?r ` ?gr"
        using dtabc_agg_group[OF f, of x rel] unfolding dtabc_def .
      have tgr: "table cs ?gr" using t by (auto simp: table_def)
      have av: "uagg_values ?g (?r ` ?gr) = (\<lambda>v. (v, ecard (Set.filter (\<lambda>x'. meval_trm cs f x' = v) ?gr)))
          ` meval_trm cs f ` ?gr"
        using uagg_values_dtabc[OF f tgr fv] unfolding dtabc_def .
      show "take ?p (drop ?m (?r x)) @ eval_agg_op \<omega>
              (uagg_values ?g (Set.filter (\<lambda>z. drop ?m z = drop ?m (?r x)) (?r ` rel)))
              # drop ?p (drop ?m (?r x))
          = restrict (merge_cols gcols [y]) (y # ?S) (?A x # agg_key ?m cs x)"
        unfolding grp av unfolding restrict_merge_single[OF sg yg] k image_image by (rule refl)
    qed
    also have "\<dots> = dtabc (y # ?S) (merge_cols gcols [y]) (eval_agg cs g0 \<omega> tys f rel)"
      unfolding dtabc_def eval_agg_def Let_def if_not_P[OF False] by (simp add: image_image)
    finally show ?thesis .
  qed
qed

section \<open>Predicates, relations, and the existential\<close>

subsection \<open>Turning a set of columns into a column list\<close>

definition set_cols :: "nat set \<Rightarrow> cols" where
  "set_cols A = csorted_list_of_set A"

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

lemma dframe_set_cols: "distinct ks \<Longrightarrow> dframe ks (set_cols (set ks))"
  by (simp add: dframe_def set_cols)

subsection \<open>Matching a predicate's arguments\<close>

text \<open>The kernel tabulates a match at the predicate's columns in their order of occurrence; the
  dense match reads it off at the same columns in ascending order.\<close>

theorem umatch_table_dtabc:
  assumes "set cs \<subseteq> set ks"
  shows "umatch_table tms cs X = dtabc ks cs (tabulate_match ks ` Option.these (match tms ` X))"
proof -
  have "umatch_table tms cs X = Option.these (map_option (\<lambda>f. map (\<lambda>c. the (f c)) cs) ` match tms ` X)"
    by (simp add: umatch_table_def umatch_match image_image)
  also have "\<dots> = (\<lambda>f. map (\<lambda>c. the (f c)) cs) ` Option.these (match tms ` X)"
    by (rule these_map_option_image)
  also have "\<dots> = dtabc ks cs (tabulate_match ks ` Option.these (match tms ` X))"
    unfolding dtabc_def image_image restrict_map tabulate_match_def
    using assms by (intro image_cong[OF refl] map_cong[OF refl]) (auto simp: tup_get_map_self)
  finally show ?thesis .
qed

subsection \<open>A predicate whose arguments are distinct variables in ascending order\<close>

text \<open>Then the kernel's columns are already ascending: the argument tuples of the database are
  the dense tuples.\<close>

fun smp_cols :: "Formula.trm list \<Rightarrow> cols" where
  "smp_cols [] = []"
| "smp_cols (Formula.Var y # ts) = y # smp_cols ts"
| "smp_cols (t # ts) = []"

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

subsection \<open>The existential\<close>

text \<open>
  The kernel drops the column of variable @{term 0} and shifts the others down by one.  Over
  ascending columns the first column is either variable @{term 0} -- and then it is the head,
  which is dropped -- or not, and then there is nothing to do.
\<close>

definition ex_drop0 :: "cols \<Rightarrow> bool" where
  "ex_drop0 ccs = (case ccs of [] \<Rightarrow> False | c # _ \<Rightarrow> c = 0)"

definition dex_cols :: "cols \<Rightarrow> cols" where
  "dex_cols ccs = map (\<lambda>c. c - Suc 0) (if ex_drop0 ccs then tl ccs else ccs)"

lemma ex_drop0_pos: "sorted_wrt (<) ccs \<Longrightarrow> \<forall>c \<in> set (if ex_drop0 ccs then tl ccs else ccs). 0 < c"
  by (cases ccs) (auto simp: ex_drop0_def)

theorem dtabc_exists:
  assumes f: "dframe ks ccs"
  shows "(if ex_drop0 ccs then tl ` dtabc ks ccs T else dtabc ks ccs T)
       = dtabc (ex_cols ks) (dex_cols ccs) (ex_proj ks ` T)"
proof -
  let ?c = "if ex_drop0 ccs then tl ccs else ccs"
  have s: "sorted_wrt (<) ccs" using dframeD(2)[OF f] .
  have l: "(if ex_drop0 ccs then tl ` dtabc ks ccs T else dtabc ks ccs T)
      = (\<lambda>x. map (tup_get ks x) ?c) ` T"
    by (auto simp: dtabc_def restrict_map map_tl)
  have cc: "c \<in> set ccs" if "c \<in> set ?c" for c
    using that by (cases ccs) (auto split: if_splits)
  have mem: "c \<in> set ks" "c \<noteq> 0" if "c \<in> set ?c" for c
    using cc[OF that] that ex_drop0_pos[OF s] dframeD(3)[OF f] by auto
  have e: "tup_get (ex_cols ks) (ex_proj ks x) (c - Suc 0) = tup_get ks x c" if "c \<in> set ?c" for x c
    using tup_get_ex_proj[of c ks x] mem[OF that] by simp
  show ?thesis
    unfolding l unfolding dtabc_def restrict_map dex_cols_def image_image
  proof (intro image_cong[OF refl])
    fix x
    show "map (tup_get ks x) ?c = map (tup_get (ex_cols ks) (ex_proj ks x)) (map (\<lambda>c. c - Suc 0) ?c)"
      unfolding map_map o_def by (rule map_cong[OF refl]) (rule e[symmetric])
  qed
qed

section \<open>The temporal operators over ascending columns\<close>

text \<open>
  The @{locale msaux} and @{locale muaux} specifications are stated over an abstract auxiliary
  list of timestamped tables, and everything they do to it is a join, a union, an intersection,
  or a filter on timestamps.  All of them commute with the reordering, so the verified structures
  can be run unchanged over the ascending columns -- which is what the theorems of this section
  say, one per operation of the two locales.
\<close>

definition dargs :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> args" where
  "dargs cs_R cs_L args = init_args (args_ivl args) (length cs_R) cs_L cs_R (args_pos args) None"

lemma dargs_simps[simp]:
  "args_ivl (dargs cs_R cs_L args) = args_ivl args"
  "args_n (dargs cs_R cs_L args) = length cs_R"
  "args_L (dargs cs_R cs_L args) = cs_L"
  "args_R (dargs cs_R cs_L args) = cs_R"
  "args_pos (dargs cs_R cs_L args) = args_pos args"
  "args_agg (dargs cs_R cs_L args) = None"
  by (simp_all add: dargs_def init_args_def)

lemma eval_args_agg_None[simp]: "args_agg args = None \<Longrightarrow> eval_args_agg args X = X"
  by (simp add: eval_args_agg_def)

text \<open>A join whose right operand's columns are among the left one's keeps the left one's columns;
  it commutes with the reordering.\<close>

theorem dtabc_join_sub:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and tR: "table kR T" and tL: "table kL U"
  shows "dtabc kR cR (join kR T pos kL U) = join cR (dtabc kR cR T) pos cL (dtabc kL cL U)"
proof -
  have sub': "set cL \<subseteq> set cR" using sub dframeD(3)[OF fR] dframeD(3)[OF fL] by simp
  have tR': "table cR (dtabc kR cR T)" and tL': "table cL (dtabc kL cL U)"
    using dtable_dtabc by (simp_all add: dtable_table[symmetric])
  have key: "restrict cL cR (restrict cR kR a) = restrict cL kL (restrict kL kR a)" for a :: "'a list"
    using sub sub' dframeD(3)[OF fR] dframeD(3)[OF fL] by (simp add: restrict_restrict)
  have mem: "(restrict cL kL (restrict kL kR a) \<in> dtabc kL cL U) = (restrict kL kR a \<in> U)" for a :: "'a list"
    by (rule dtabc_in_iff[OF fL tL]) simp
  show ?thesis
    unfolding join_sub_eq[OF dframeD(1)[OF fR] dframeD(1)[OF fL] tR tL sub]
      join_sub_eq[OF dframeD(4)[OF fR] dframeD(4)[OF fL] tR' tL' sub']
  proof (intro equalityI subsetI)
    fix d assume "d \<in> dtabc kR cR {a \<in> T. (restrict kL kR a \<in> U) = pos}"
    then obtain a where a: "a \<in> T" "(restrict kL kR a \<in> U) = pos" "d = restrict cR kR a"
      by (auto simp: dtabc_def)
    have "d \<in> dtabc kR cR T" using a(1,3) by (auto simp: dtabc_def)
    then show "d \<in> {d \<in> dtabc kR cR T. (restrict cL cR d \<in> dtabc kL cL U) = pos}"
      using a(2,3) by (simp add: key mem)
  next
    fix d assume d: "d \<in> {d \<in> dtabc kR cR T. (restrict cL cR d \<in> dtabc kL cL U) = pos}"
    then obtain a where a: "a \<in> T" "d = restrict cR kR a" by (auto simp: dtabc_def)
    then have "(restrict kL kR a \<in> U) = pos" using d by (simp add: key mem)
    then show "d \<in> dtabc kR cR {a \<in> T. (restrict kL kR a \<in> U) = pos}"
      using a unfolding dtabc_def by blast
  qed
qed

lemma table_join_sub: "table kR X \<Longrightarrow> table kL Y \<Longrightarrow> set kL \<subseteq> set kR \<Longrightarrow> table kR (join kR X b kL Y)"
  by (rule join_table[of kR X kL Y b kR]) (auto simp: cols_union_def filter_empty_conv)

subsection \<open>The Since structure's auxiliary list\<close>

definition dauxlist :: "cols \<Rightarrow> cols \<Rightarrow> (ts \<times> 'b list set) list \<Rightarrow> (ts \<times> 'b list set) list" where
  "dauxlist ks cs aux = map (\<lambda>(t, rel). (t, dtabc ks cs rel)) aux"

lemma dauxlist_filter:
  "dauxlist ks cs (filter (\<lambda>(t, rel). P t) aux) = filter (\<lambda>(t, rel). P t) (dauxlist ks cs aux)"
  by (induct aux) (auto simp: dauxlist_def)

lemma dauxlist_join:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and wf: "\<forall>(t, rel) \<in> set aux. table kR rel" and t1: "table kL rel1"
  shows "dauxlist kR cR (map (\<lambda>(t, rel). (t, join kR rel pos kL rel1)) aux)
       = map (\<lambda>(t, rel). (t, join cR rel pos cL (dtabc kL cL rel1))) (dauxlist kR cR aux)"
  using wf by (induct aux) (auto simp: dauxlist_def dtabc_join_sub[OF fR fL sub _ t1])

lemma dauxlist_add_new_table:
  "dauxlist ks cs (case aux of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # aux)
   = (case dauxlist ks cs aux of [] \<Rightarrow> [(cur, dtabc ks cs rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc ks cs rel2) # r
                         else (cur, dtabc ks cs rel2) # dauxlist ks cs aux)"
  by (cases aux) (auto simp: dauxlist_def dtabc_Un_img)

lemma dtabc_result:
  "dtabc ks cs (foldr (\<union>) [rel. (t, rel) \<leftarrow> aux, P t] {})
     = foldr (\<union>) [rel. (t, rel) \<leftarrow> dauxlist ks cs aux, P t] {}"
  by (induct aux) (auto simp: dauxlist_def dtabc_Un_img)

lemma dauxlist_wf_join:
  assumes "\<forall>(t, rel) \<in> set aux. table kR rel" and "set kL \<subseteq> set kR" and "table kL rel1"
  shows "\<forall>(t, rel) \<in> set (map (\<lambda>(t, rel). (t, join kR rel pos kL rel1)) aux). table kR rel"
  using assms by (auto intro: table_join_sub)

lemma dauxlist_wf_add_new_table:
  assumes "\<forall>(t, rel) \<in> set aux. table ks rel" and "table ks rel2"
  shows "\<forall>(t, rel) \<in> set (case aux of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # aux). table ks rel"
  using assms by (cases aux) (auto simp: table_def)

subsection \<open>The Until structure's auxiliary list\<close>

definition dauxlist3 :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) list" where
  "dauxlist3 kL cL kR cR aux = map (\<lambda>(t, a1, a2). (t, dtabc kL cL a1, dtabc kR cR a2)) aux"

lemma dauxlist3_update_until:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and wf: "\<forall>(t, a1, a2) \<in> set aux. table kL a1 \<and> table kR a2"
    and t1: "table kL rel1" and t2: "table kR rel2"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and aL': "args_L args' = cL" and aR': "args_R args' = cR"
    and iv: "args_ivl args' = args_ivl args" and po: "args_pos args' = args_pos args"
  shows "dauxlist3 kL cL kR cR (update_until args rel1 rel2 nt aux)
       = update_until args' (dtabc kL cL rel1) (dtabc kR cR rel2) nt (dauxlist3 kL cL kR cR aux)"
  using wf
  by (induct aux)
    (auto simp: dauxlist3_def update_until_def iv po aL aR aL' aR' empty_table_def dtabc_Un_img
       dtabc_Int[OF fL _ t1] dtabc_join_sub[OF fR fL sub t2])

lemma dauxlist3_eval_until:
  "eval_until I nt aux = (res, aux') \<Longrightarrow>
     eval_until I nt (dauxlist3 kL cL kR cR aux) = (map (dtabc kR cR) res, dauxlist3 kL cL kR cR aux')"
  by (induct I nt aux arbitrary: res aux' rule: eval_until.induct)
    (auto simp: dauxlist3_def split: if_splits prod.splits)

lemma table_Un: "table ks X \<Longrightarrow> table ks Y \<Longrightarrow> table ks (X \<union> Y)"
  by (auto simp: table_def)

lemma table_Int: "table ks X \<Longrightarrow> table ks (X \<inter> Y)"
  by (auto simp: table_def)

lemma dauxlist3_wf_update_until:
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

section \<open>Buffers of reordered tables\<close>

text \<open>
  A buffer never looks inside a tuple: it lines up the tables the operands produce and hands
  matching pairs to the node's operation.  So a buffer of reordered tables behaves as the
  reordering of a buffer of the kernel's.  These are map-fusion lemmas for the kernel's own
  list-level buffers, which is where its verified @{const meval} lives.
\<close>

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

lemma mbuf2t_take_rel:
  "(\<And>a b t z z'. a \<in> set xs \<Longrightarrow> b \<in> set ys \<Longrightarrow> R z z' \<Longrightarrow>
      R (f a b t z) (g (h a) (k b) t z')) \<Longrightarrow>
   R z z' \<Longrightarrow>
   mbuf2t_take f z (xs, ys) t0 ts = (w, (xs', ys'), nt, ts') \<Longrightarrow>
   mbuf2t_take g z' (map h xs, map k ys) t0 ts = (w2, buf2, nt2, ts2) \<Longrightarrow>
   R w w2 \<and> buf2 = (map h xs', map k ys') \<and> nt2 = nt \<and> ts2 = ts'"
proof (induct xs arbitrary: ys z z' t0 ts w xs' ys' nt ts' w2 buf2 nt2 ts2)
  case Nil
  then show ?case by (auto split: list.splits)
next
  case (Cons x xs)
  note IH = Cons(1) and P1 = Cons(2) and P2 = Cons(3) and P3 = Cons(4) and P4 = Cons(5)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using P2 P3 P4 by (auto split: list.splits)
  next
    case (Cons y ys2)
    note ysC = Cons
    show ?thesis
    proof (cases ts)
      case Nil
      then show ?thesis using P2 P3 P4 ysC by simp
    next
      case (Cons t ts3)
      note tsC = Cons
      have r: "R (f x y t z) (g (h x) (k y) t z')" using P1 P2 ysC by simp
      have p1: "\<And>a b t' za z'a. a \<in> set xs \<Longrightarrow> b \<in> set ys2 \<Longrightarrow> R za z'a \<Longrightarrow>
          R (f a b t' za) (g (h a) (k b) t' z'a)" using P1 ysC by simp
      have s1: "mbuf2t_take f (f x y t z) (xs, ys2) t ts3 = (w, (xs', ys'), nt, ts')"
        using P3 ysC tsC by simp
      have s2: "mbuf2t_take g (g (h x) (k y) t z') (map h xs, map k ys2) t ts3
          = (w2, buf2, nt2, ts2)"
        using P4 ysC tsC by simp
      show ?thesis by (rule IH[OF p1 r s1 s2])
    qed
  qed
qed

text \<open>
  The Until node's operation is the one place where the step condition is not uniform in the
  timestamp: the verified structure accepts a new timestamp only at or after the one it is already
  at.  So the accumulator relation is indexed by that timestamp, the step may assume the new one
  is no smaller, and the conclusion says where the accumulator ended up -- at or before the
  timestamp the buffer reports and at or before every timestamp it did not consume.
\<close>

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

subsection \<open>The multi-way buffer\<close>

text \<open>
  @{const mbufn_take} lines up one table per conjunct, and each conjunct has its own column list,
  so the morphism is a list of reorderings applied slotwise.  The step condition is relational for
  the same reason as @{thm [source] mbuf2t_take_rel}, and it is restricted to tables drawn from
  fixed sets @{term Ss}, one per slot, because the tables the operands produce have to be well
  formed for the multi-way join theorem to apply and the buffer only ever shrinks.
\<close>

lemma length_map2_map[simp]: "length hs = length buf \<Longrightarrow> length (map2 map hs buf) = length buf"
  by simp

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

subsection \<open>Leftovers of a buffer\<close>

text \<open>A take only ever removes a prefix, so whatever stays in the buffer was already there.\<close>

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

text \<open>The same two facts for the timestamped take: what it leaves in the buffers is a
  sublist of what it found there, and two runs whose buffers differ by a map on each operand
  step together, consume the same timestamps and leave buffers that differ by the same map.
  The past and future match nodes need them, as the conjunction nodes need the untimed ones.\<close>

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

subsection \<open>Leftovers of the shift buffer\<close>

lemma mprev_next_sub: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow> set xs' \<subseteq> set xs"
  by (induct I xs ts arbitrary: ys xs' ts' rule: mprev_next.induct)
    (auto split: prod.splits)

section \<open>The unit and empty tables\<close>

lemma dtabc_unit_table: "dtabc [] [] unit_table = unit_table"
  by (simp add: dtabc_def unit_table_def)

text \<open>Hence a negation node, whose operand has no columns at all, only has to look at
  emptiness -- which the reordering preserves in both directions.\<close>

lemma dtabc_empty_table[simp]: "dtabc ks cs empty_table = empty_table"
  by (simp add: empty_table_def)

section \<open>The multi-way join the monitor runs\<close>

text \<open>This is the shape the evaluator calls: one plan list for the positive operands, one for
  the negative ones, and the operand tables as a single list.\<close>

definition dmulti_join :: "djoin_plan list \<Rightarrow> djoin_plan list \<Rightarrow>
    event_data table list \<Rightarrow> event_data table" where
  "dmulti_join ps ns us = (case us of [] \<Rightarrow> empty_table
     | t # r \<Rightarrow> dands_neg ns (dands_pos ps t (take (length ps) r)) (drop (length ps) r))"

lemma length_dands_plans[simp]: "length (dands_plans acc css) = length css"
  by (induct css arbitrary: acc) auto

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
    and "list_all2 dframe (map fst kcs) (map snd kcs)"
  using assms by (auto simp: list_all2_conv_all_nth set_zip wf_operand_def case_prod_beta
      dframe_def)

theorem dmulti_join_eq:
  assumes f0: "dframe k0 c0" and t0: "table k0 T0" and fT0: "finite T0"
    and pos: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) kcs Us"
    and neg: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) nkcs Vs"
    and sub: "\<forall>c \<in> set (map snd nkcs). set c \<subseteq> set (dands_cols c0 (map snd kcs))"
    and cs: "distinct cs" "set cs = set (kands_cols k0 (map fst kcs))"
  shows "dmulti_join (dands_plans c0 (map snd kcs))
           (dands_plans (dands_cols c0 (map snd kcs)) (map snd nkcs))
           (map2 (\<lambda>(k, c). dtabc k c) ((k0, c0) # kcs @ nkcs) ((T0 # Us) @ Vs))
       = dtabc cs (dands_cols c0 (map snd kcs))
           (mmulti_join cs (k0 # map fst kcs) (map fst nkcs) ((T0 # Us) @ Vs))"
proof -
  let ?K = "kands_cols k0 (map fst kcs)" and ?C = "dands_cols c0 (map snd kcs)"
  let ?P = "kands_pos k0 T0 (zip (map fst kcs) Us)"
  have lp: "length kcs = length Us" using pos by (rule list_all2_lengthD)
  have ln: "length nkcs = length Vs" using neg by (rule list_all2_lengthD)
  note wp = wf_operands_zip[OF pos] and wn = wf_operands_zip[OF neg]
  have dk0: "distinct k0" using dframeD(1)[OF f0] .
  have fK: "dframe ?K ?C" by (rule dframe_dands_cols[OF wp(3) f0])
  have wp1: "\<forall>(k, u) \<in> set (zip (map fst kcs) Us). distinct k \<and> table k u" using wp(1) by auto
  have tP: "table ?K ?P"
    unfolding table_def using kands_pos_iff[OF dk0 t0 wp1] wp(2) by simp
  have fP: "finite ?P" by (rule finite_kands_pos[OF fT0]) (use wp(1) in auto)
  have subK: "\<forall>(k, u) \<in> set (zip (map fst nkcs) Vs). distinct k \<and> table k u \<and> set k \<subseteq> set ?K"
  proof (intro ballI, clarify)
    fix k u assume ku: "(k, u) \<in> set (zip (map fst nkcs) Vs)"
    then obtain i where i: "i < length nkcs" "k = fst (nkcs ! i)" "u = Vs ! i"
      using ln by (auto simp: in_set_zip)
    have "dframe k (snd (nkcs ! i))" using wn(3) i by (auto simp: list_all2_conv_all_nth)
    moreover have "set (snd (nkcs ! i)) \<subseteq> set ?C" using sub i by auto
    moreover have "set ?C = set ?K" using dframeD(3)[OF fK] .
    ultimately show "distinct k \<and> table k u \<and> set k \<subseteq> set ?K"
      using wn(1) ku by (auto simp: dframe_def)
  qed
  have m: "map2 (\<lambda>(k, c). dtabc k c) ((k0, c0) # kcs @ nkcs) ((T0 # Us) @ Vs)
      = dtabc k0 c0 T0 # (map2 (\<lambda>(k, c). dtabc k c) kcs Us @ map2 (\<lambda>(k, c). dtabc k c) nkcs Vs)"
    by (simp add: map2_append[OF lp])
  have "dmulti_join (dands_plans c0 (map snd kcs)) (dands_plans ?C (map snd nkcs))
          (map2 (\<lambda>(k, c). dtabc k c) ((k0, c0) # kcs @ nkcs) ((T0 # Us) @ Vs))
      = dands_neg (dands_plans ?C (map snd nkcs))
          (dands_pos (dands_plans c0 (map snd kcs)) (dtabc k0 c0 T0)
            (map2 (\<lambda>(k, c). dtabc k c) kcs Us))
          (map2 (\<lambda>(k, c). dtabc k c) nkcs Vs)"
    unfolding dmulti_join_def m using lp by simp
  also have "\<dots> = dands_neg (dands_plans ?C (map snd nkcs)) (dtabc ?K ?C ?P)
      (map2 (\<lambda>(k, c). dtabc k c) nkcs Vs)"
    by (simp only: dands_pos_dtabc[OF f0 t0 fT0 pos])
  also have "\<dots> = dtabc ?K ?C (kands_neg ?K ?P (zip (map fst nkcs) Vs))"
    by (rule dands_neg_dtabc[OF fK tP fP neg sub])
  also have "\<dots> = dtabc cs ?C (restrict cs ?K ` kands_neg ?K ?P (zip (map fst nkcs) Vs))"
  proof -
    have "table ?K (kands_neg ?K ?P (zip (map fst nkcs) Vs))"
      using kands_neg_iff[OF dframeD(1)[OF fK] tP subK] tP by (auto simp: table_def)
    then show ?thesis by (rule dtabc_restrict[OF fK cs(2), symmetric])
  qed
  also have "\<dots> = dtabc cs ?C (mmulti_join cs (k0 # map fst kcs) (map fst nkcs) ((T0 # Us) @ Vs))"
  proof -
    have "mmulti_join cs (k0 # map fst kcs) (map fst nkcs) ((T0 # Us) @ Vs)
        = restrict cs ?K ` kands_neg ?K ?P (zip (map fst nkcs) Vs)"
      by (rule mmulti_join_kands[OF dk0 t0 wp1 wp(2) subK _ cs]) (simp add: ln)
    then show ?thesis by (simp only:)
  qed
  finally show ?thesis .
qed

section \<open>Comparisons on dense tuples\<close>

text \<open>
  A constraint node only filters; it never changes a tuple.  Reindexing its two terms against
  the node's column list makes the filter read the dense tuple at the position the column
  occupies there, which by @{thm [source] umeval_trm_reindex} evaluates to the same value.
  Filtering commutes with an image without any injectivity, so the reordering passes through.
\<close>

definition reindex_constraint ::
    "cols \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow>
     Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm" where
  "reindex_constraint cs conf = (case conf of (t1, p, c, t2) \<Rightarrow>
     (reindex_trm cs t1, p, c, reindex_trm cs t2))"

theorem ueval_constraint_reindex:
  assumes fv1: "Formula.fv_trm t1 \<subseteq> set cs" and fv2: "Formula.fv_trm t2 \<subseteq> set cs"
  shows "dtabc ks cs (Set.filter (eval_constraint ks (t1, p, c, t2)) T)
       = Set.filter (ueval_constraint (reindex_constraint cs (t1, p, c, t2))) (dtabc ks cs T)"
proof -
  have "ueval_constraint (reindex_constraint cs (t1, p, c, t2)) (restrict cs ks x)
      = eval_constraint ks (t1, p, c, t2) x" for x
    by (simp add: reindex_constraint_def ueval_constraint_def
        umeval_trm_reindex[OF fv1] umeval_trm_reindex[OF fv2])
  then show ?thesis unfolding dtabc_def by auto
qed

section \<open>The plan of a left operand inside the right one's frame\<close>

text \<open>A Since structure joins its left operand into the running tables: the plan records, for each
  column of the right operand, the position the column occupies among the left operand's, if any.
  It is computed once, when the formula is compiled.\<close>

definition emb_plan :: "cols \<Rightarrow> cols \<Rightarrow> nat option list" where
  "emb_plan cs_R cs_L = map (\<lambda>c. if c \<in> set cs_L then Some (col_pos cs_L c) else None) cs_R"

section \<open>The assignment, the time point and the timestamp\<close>

subsection \<open>Assigning a term to a fresh column\<close>

text \<open>
  The kernel's assignment appends the value at the end of its tuple:
  @{thm eval_assignment.simps}.  The dense tuple has it at the position the new column occupies
  in the merged column list -- the same insertion the aggregation's output does, at the same
  @{const ins_pos}.
\<close>

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
  assumes f: "dframe ks cs" and y: "y \<notin> set ks" and fv: "Formula.fv_trm t \<subseteq> set cs"
    and tT: "table ks T"
  shows "uassign (ins_pos cs y) (reindex_trm cs t) (dtabc ks cs T)
       = dtabc (ks @ [y]) (merge_cols cs [y]) (eval_assignment ks (y, t) ` T)"
proof -
  have "uassign1 (ins_pos cs y) (reindex_trm cs t) (restrict cs ks x)
      = restrict (merge_cols cs [y]) (ks @ [y]) (eval_assignment ks (y, t) x)" if "x \<in> T" for x
  proof -
    have w: "wf_tuple ks x" using tT that by (simp add: table_def)
    show ?thesis
      unfolding uassign1_def eval_assignment.simps umeval_trm_reindex[OF fv]
      by (rule restrict_merge_single_append[symmetric, OF dframeD(2)[OF f] y _ w])
        (use dframeD(3)[OF f] in simp)
  qed
  then show ?thesis unfolding uassign_def dtabc_def image_image by (auto intro!: image_cong)
qed

text \<open>The operand's column list is the node's without the assigned column, and putting the
  latter back is the merge the theorem above asks for.\<close>

subsection \<open>The time point and the timestamp\<close>

text \<open>
  The two nodes that turn a number into a table produce either a one-column table holding that
  number or a zero-column truth value; the kernel's tables are already the dense ones.
\<close>

definition mtrm_dcols :: "mtrm \<Rightarrow> cols" where
  "mtrm_dcols mt = (case mt of MVar v \<Rightarrow> [v] | MConst c \<Rightarrow> [])"

theorem umtrm_eval_mtrm: "umtrm mt x = eval_mtrm mt x"
  by (cases mt) (simp_all add: singleton_table_def unit_table_def empty_table_def)

lemma table_dtabc: "table cs (dtabc ks cs T)"
  using dtable_dtabc by (simp add: dtable_table[symmetric])

section \<open>The verified Trigger structure over ascending columns\<close>

text \<open>
  The trigger's auxiliary list carries two tables per time point, like the Until's, but the
  structure reads its answer off that list rather than accumulating it, so what has to transport
  is @{const trigger_results} itself.  Its \<^emph>\<open>then\<close> branch is a set comprehension over tuples of
  the right operand's columns, and the two conditions it puts on a tuple -- membership in a
  stored right table, and a join against a stored left table -- both commute with the reordering.
\<close>

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

lemma length_filter_dauxlist3:
  "length (filter (\<lambda>(t, _, _). P t) (dauxlist3 kL cL kR cR auxlist))
     = length (filter (\<lambda>(t, _, _). P t) auxlist)"
  by (induct auxlist) (auto simp: dauxlist3_def)

lemma nth_dauxlist3:
  "i < length auxlist \<Longrightarrow> dauxlist3 kL cL kR cR auxlist ! i =
     (fst (auxlist ! i), dtabc kL cL (fst (snd (auxlist ! i))), dtabc kR cR (snd (snd (auxlist ! i))))"
  by (simp add: dauxlist3_def case_prod_beta)

lemma length_dauxlist3[simp]: "length (dauxlist3 kL cL kR cR auxlist) = length auxlist"
  by (simp add: dauxlist3_def)

theorem dtabc_trigger_results:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and wf: "\<forall>(t, l, r) \<in> set auxlist. table kL l \<and> table kR r"
  shows "dframe (fst (trigger_results args cur auxlist))
           (fst (trigger_results (dargs cR cL args) cur (dauxlist3 kL cL kR cR auxlist)))"
    and "snd (trigger_results (dargs cR cL args) cur (dauxlist3 kL cL kR cR auxlist))
       = dtabc (fst (trigger_results args cur auxlist))
           (fst (trigger_results (dargs cR cL args) cur (dauxlist3 kL cL kR cR auxlist)))
           (snd (trigger_results args cur auxlist))"
proof -
  let ?I = "args_ivl args" and ?p = "args_pos args"
  let ?da = "dauxlist3 kL cL kR cR auxlist"
  have sub': "set cL \<subseteq> set cR" using sub dframeD(3)[OF fR] dframeD(3)[OF fL] by simp
  have tl: "table kL (fst (snd (auxlist ! i)))" and tr: "table kR (snd (snd (auxlist ! i)))"
    if "i < length auxlist" for i
    using wf nth_mem[OF that] by (auto simp: case_prod_beta)
  have key: "restrict cL cR (restrict cR kR a) = restrict cL kL (restrict kL kR a)" for a :: "event_data tuple"
    using sub sub' dframeD(3)[OF fR] dframeD(3)[OF fL] by (simp add: restrict_restrict)
  define P where "P a \<longleftrightarrow> (\<forall>i < length auxlist. mem ?I (cur - fst (auxlist ! i)) \<longrightarrow>
      (a \<in> snd (snd (auxlist ! i)) \<or>
       (\<exists>j. i < j \<and> j < length auxlist \<and>
          join_cond ?p (fst (snd (auxlist ! j))) (restrict kL kR a))))" for a :: "event_data tuple"
  define Q where "Q d \<longleftrightarrow> (\<forall>i < length auxlist. mem ?I (cur - fst (auxlist ! i)) \<longrightarrow>
      (d \<in> dtabc kR cR (snd (snd (auxlist ! i))) \<or>
       (\<exists>j. i < j \<and> j < length auxlist \<and>
          join_cond ?p (dtabc kL cL (fst (snd (auxlist ! j)))) (restrict cL cR d))))"
    for d :: "event_data tuple"
  \<comment> \<open>the two conditions the comprehension puts on a tuple\<close>
  have cond: "Q (restrict cR kR a) = P a" if wa: "wf_tuple kR a" for a :: "event_data tuple"
  proof -
    have inR: "(restrict cR kR a \<in> dtabc kR cR (snd (snd (auxlist ! i)))) = (a \<in> snd (snd (auxlist ! i)))"
      if "i < length auxlist" for i
      by (rule dtabc_in_iff[OF fR tr[OF that] wa])
    have inL: "(restrict cL cR (restrict cR kR a) \<in> dtabc kL cL (fst (snd (auxlist ! j))))
        = (restrict kL kR a \<in> fst (snd (auxlist ! j)))" if "j < length auxlist" for j
      unfolding key by (rule dtabc_in_iff[OF fL tl[OF that]]) simp
    show ?thesis unfolding P_def Q_def by (auto simp: inR inL)
  qed
  have DS: "{d. wf_tuple cR d \<and> Q d} = dtabc kR cR {a. wf_tuple kR a \<and> P a}"
  proof (intro set_eqI iffI)
    fix d assume d: "d \<in> {d. wf_tuple cR d \<and> Q d}"
    let ?a = "restrict kR cR d"
    have ld: "length d = length cR" using d by (simp add: wf_tuple_def)
    have da: "restrict cR kR ?a = d" by (rule restrict_inv'[OF fR ld])
    have "P ?a" using d cond[of ?a] da by simp
    then have "?a \<in> {a. wf_tuple kR a \<and> P a}" by simp
    then show "d \<in> dtabc kR cR {a. wf_tuple kR a \<and> P a}"
      unfolding dtabc_def using da by (metis image_eqI)
  next
    fix d assume "d \<in> dtabc kR cR {a. wf_tuple kR a \<and> P a}"
    then obtain a where a: "wf_tuple kR a" "P a" and da: "d = restrict cR kR a"
      unfolding dtabc_def by auto
    show "d \<in> {d. wf_tuple cR d \<and> Q d}" using cond[OF a(1)] a(2) da by simp
  qed
  have flt: "length (filter (\<lambda>(t, _, _). mem ?I (cur - t)) ?da)
      = length (filter (\<lambda>(t, _, _). mem ?I (cur - t)) auxlist)"
    by (rule length_filter_dauxlist3)
  have dset: "{tuple. wf_tuple cR tuple \<and>
      (\<forall>i < length ?da. mem ?I (cur - fst (?da ! i)) \<longrightarrow>
         (tuple \<in> snd (snd (?da ! i)) \<or>
          (\<exists>j. i < j \<and> j < length ?da \<and>
             join_cond ?p (fst (snd (?da ! j))) (restrict cL cR tuple))))}
    = {d. wf_tuple cR d \<and> Q d}"
    by (auto simp: Q_def nth_dauxlist3)
  have dsimp: "trigger_results (dargs cR cL args) cur ?da
      = (if 0 < length (filter (\<lambda>(t, _, _). mem ?I (cur - t)) auxlist)
         then (cR, {d. wf_tuple cR d \<and> Q d}) else ([], unit_table))"
    by (simp only: trigger_results_eq flt dargs_simps dset)
  have ssimp: "trigger_results args cur auxlist
      = (if 0 < length (filter (\<lambda>(t, _, _). mem ?I (cur - t)) auxlist)
         then (kR, {a. wf_tuple kR a \<and> P a}) else ([], unit_table))"
    by (simp only: trigger_results_eq aL aR P_def)
  show "dframe (fst (trigger_results args cur auxlist))
      (fst (trigger_results (dargs cR cL args) cur ?da))"
    unfolding dsimp ssimp using fR by (simp add: dframe_def)
  show "snd (trigger_results (dargs cR cL args) cur ?da)
       = dtabc (fst (trigger_results args cur auxlist)) (fst (trigger_results (dargs cR cL args) cur ?da))
           (snd (trigger_results args cur auxlist))"
    unfolding dsimp ssimp using DS by (simp add: dtabc_unit_table)
qed

text \<open>The structure over ascending columns, related to the kernel's through the abstract
  auxiliary list they are both valid for, exactly as for the Since and the Until.\<close>

lemma dauxlist3_filter_append:
  "dauxlist3 kL cL kR cR (filter (\<lambda>(t, _). P t) auxlist @ [(nt, l, r)])
     = filter (\<lambda>(t, _). P t) (dauxlist3 kL cL kR cR auxlist) @ [(nt, dtabc kL cL l, dtabc kR cR r)]"
  by (induct auxlist) (auto simp: dauxlist3_def)

text \<open>The trigger's buffer traversal, stepped over both column orders at once.  It is
  @{thm [source] mbuf2t_take_rel_ts} without the timestamp bookkeeping.\<close>

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

section \<open>An index for the dense semi-join\<close>

text \<open>
  The Since and the Until probe their stored tables with the left operand's table.  Over ascending
  columns the probe table \<^emph>\<open>is\<close> the key set: a stored tuple is kept exactly when its projection at
  the merge plan's key mask is in the probe table, or, for a negative operand, out of it.  So the
  index is a plain clustering of the stored table by that projection, and the probe is a
  restriction of the mapping.
\<close>

definition didx :: "bool list \<Rightarrow> 'b list set \<Rightarrow> ('b list, 'b list set) mapping" where
  "didx msk T = cluster (Some \<circ> dproj msk) T"

definition dsemi_idx :: "bool list \<Rightarrow> bool \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow> 'b list set \<Rightarrow>
    'b list set" where
  "dsemi_idx msk pos idx X = set_of_idx (Mapping.filter (\<lambda>k _. (k \<in> X) = pos) idx)"

lemma in_set_of_idx: "(y \<in> set_of_idx m) = (\<exists>k Y. Mapping.lookup m k = Some Y \<and> y \<in> Y)"
  by transfer (auto simp: ran_def)

lemma lookup_didx: "Mapping.lookup (didx msk T) k =
  (if k \<in> dproj msk ` T then Some {y \<in> T. dproj msk y = k} else None)"
  unfolding didx_def by transfer auto

text \<open>The index computes the semi-join: a stored tuple's bucket survives the restriction exactly
  when the tuple itself survives the filter.\<close>

theorem dsemi_idx_dsemi: "dsemi_idx msk pos (didx msk T) X = dsemi msk pos T X"
proof (intro set_eqI iffI)
  fix y assume "y \<in> dsemi_idx msk pos (didx msk T) X"
  then show "y \<in> dsemi msk pos T X"
    by (auto simp: dsemi_idx_def dsemi_def in_set_of_idx Mapping.lookup_filter lookup_didx
        split: if_splits option.splits)
next
  fix y assume "y \<in> dsemi msk pos T X"
  then have yT: "y \<in> T" and yp: "(dproj msk y \<in> X) = pos" by (auto simp: dsemi_def)
  have "Mapping.lookup (Mapping.filter (\<lambda>k _. (k \<in> X) = pos) (didx msk T)) (dproj msk y)
      = Some {z \<in> T. dproj msk z = dproj msk y}"
    using yT yp by (simp add: Mapping.lookup_filter lookup_didx)
  then show "y \<in> dsemi_idx msk pos (didx msk T) X"
    using yT by (auto simp: dsemi_idx_def in_set_of_idx)
qed

(*<*)
end
(*>*)
