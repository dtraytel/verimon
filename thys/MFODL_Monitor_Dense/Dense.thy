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

lemma dframe_length: "dframe ks cs \<Longrightarrow> length cs = length ks"
  by (metis dframeD(1,3,4) distinct_card)

text \<open>The dense projection by a mask, used between dense frames.\<close>

fun dproj :: "bool list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "dproj [] xs = []"
| "dproj (True # bs) (x # xs) = x # dproj bs xs"
| "dproj (False # bs) (x # xs) = dproj bs xs"
| "dproj (b # bs) [] = []"

lemma length_dproj: "length bs = length xs \<Longrightarrow> length (dproj bs xs) = length (filter id bs)"
  by (induct bs xs rule: dproj.induct) auto

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

lemma dtabc_inj:
  "dframe ks cs \<Longrightarrow> table ks T \<Longrightarrow> table ks T' \<Longrightarrow> dtabc ks cs T = dtabc ks cs T' \<Longrightarrow> T = T'"
  by (metis (no_types, lifting) dtabc_in_iff table_def subsetI subset_antisym)

lemma dtable_dtabc: "dtable cs (dtabc ks cs T)"
  by (auto simp: dtable_def dtabc_def)

lemma table_dtabw: "table ks (dtabw ks cs D)"
  by (auto simp: dtabw_def table_def)

lemma dtabw_dtabc: "dframe ks cs \<Longrightarrow> table ks T \<Longrightarrow> dtabw ks cs (dtabc ks cs T) = T"
  by (force simp: dtabw_def dtabc_def table_def restrict_inv image_image)

lemma dtabc_dtabw: "dframe ks cs \<Longrightarrow> dtable cs D \<Longrightarrow> dtabc ks cs (dtabw ks cs D) = D"
  by (force simp: dtabw_def dtabc_def dtable_def restrict_inv' image_image)

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

lemma dtabc_Diff:
  assumes f: "dframe ks cs" and t1: "table ks T" and t2: "table ks T'"
  shows "dtabc ks cs (T - T') = dtabc ks cs T - dtabc ks cs T'"
proof (intro equalityI subsetI)
  fix z assume "z \<in> dtabc ks cs (T - T')"
  then obtain a where a: "a \<in> T" "a \<notin> T'" "z = restrict cs ks a" by (auto simp: dtabc_def)
  have "z \<notin> dtabc ks cs T'"
  proof
    assume "z \<in> dtabc ks cs T'"
    then obtain a' where a': "a' \<in> T'" "z = restrict cs ks a'" by (auto simp: dtabc_def)
    have "wf_tuple ks a" "wf_tuple ks a'" using a(1) a'(1) t1 t2 by (auto simp: table_def)
    then have "a = a'" using restrict_inv[OF f] a(3) a'(2) by metis
    then show False using a(2) a'(1) by simp
  qed
  then show "z \<in> dtabc ks cs T - dtabc ks cs T'" using a by (auto simp: dtabc_def)
qed (auto simp: dtabc_def)

lemma dtabc_Un: "dtabc ks cs (T \<union> T') = dtabc ks cs T \<union> dtabc ks cs T'"
  by (rule dtabc_Un_img)

subsection \<open>Equal columns, and a right operand with no columns\<close>

lemma mrg_plan_self: "mrg_plan cs cs = map (\<lambda>_. MBth) cs"
  by (induct cs) auto

lemma mrg_left_key_MBth: "mrg_left_key (map (\<lambda>_. MBth) cs) = map (\<lambda>_. True) cs"
  by (induct cs) auto

lemma dproj_all_True_map: "length xs = length cs \<Longrightarrow> dproj (map (\<lambda>_. True) cs) xs = xs"
  by (induct cs arbitrary: xs) (auto simp: length_Suc_conv)

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

corollary dbin_join_bin_join:
  assumes f1: "dframe ks1 cs1" and f2: "dframe ks2 cs2"
    and t1: "table ks1 T" and t2: "table ks2 T'"
    and neg: "\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1"
    and fT: "finite T" and fT': "finite T'"
  shows "dbin_join (mk_djoin cs1 cs2) (dtabc ks1 cs1 T) pos (dtabc ks2 cs2 T')
       = dtabc (cols_union ks1 ks2) (merge_cols cs1 cs2) (bin_join ks1 T pos ks2 T')"
  unfolding bin_join_table[OF dframeD(1)[OF f1] dframeD(1)[OF f2] t1 t2]
  by (rule dbin_join_join[OF f1 f2 t1 t2 neg fT fT'])

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

lemma set_dands_cols: "set (dands_cols acc css) = set acc \<union> (\<Union>c \<in> set css. set c)"
  by (induct css arbitrary: acc) (auto simp: set_merge_cols)

lemma sorted_dands_cols:
  "sorted_wrt (<) acc \<Longrightarrow> \<forall>c \<in> set css. sorted_wrt (<) c \<Longrightarrow> sorted_wrt (<) (dands_cols acc css)"
  by (induct css arbitrary: acc) (auto simp: sorted_merge_cols)

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

lemma agg_cols_sorted: "sorted_wrt (<) gcols \<Longrightarrow> sorted_wrt (<) (agg_cols m gcols)"
  by (auto simp: sorted_wrt_append sorted_wrt_map)

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

(*<*)
end
(*>*)
