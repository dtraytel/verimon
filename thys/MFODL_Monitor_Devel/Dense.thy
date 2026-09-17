(*<*)
theory Dense
  imports "MFODL_Monitor_Devel.Code_Opt"
begin
(*>*)

section \<open>Tuples without their empty columns: the verified core\<close>

text \<open>
  A table of the monitor is a set of tuples all of one width, and @{const wf_tuple} says a tuple
  carries @{const None} at exactly the positions outside the free variables of the subformula
  that produced it.  Those positions are the same for every tuple of a table and are known from
  the formula, so they can be deleted and the column list kept in the formula instead.

  This theory proves that deleting them loses nothing: the projection and its inverse are
  mutually inverse on well-formed tuples and injective on a table, and the join over the short
  tuples agrees with @{const join1} over the wide ones.  The definitions are the ones the
  monitor of @{file "../MFODL_Monitor_Imp/Dense_Imp.thy"} runs; that theory will import this one
  once the remaining layers (the table join, the aggregation, and the evaluation function) are
  proved as well.
\<close>

type_synonym cols = "nat list"

fun dproj :: "bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "dproj [] xs = []"
| "dproj (True # bs) (x # xs) = x # dproj bs xs"
| "dproj (False # bs) (x # xs) = dproj bs xs"
| "dproj (b # bs) [] = []"

fun dwiden :: "bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "dwiden [] xs = []"
| "dwiden (False # bs) xs = None # dwiden bs xs"
| "dwiden (True # bs) (x # xs) = x # dwiden bs xs"
| "dwiden (True # bs) [] = []"

fun wide_mask_at :: "nat \<Rightarrow> nat \<Rightarrow> cols \<Rightarrow> bool list" where
  "wide_mask_at i 0 cs = []"
| "wide_mask_at i (Suc k) cs =
     (case cs of [] \<Rightarrow> False # wide_mask_at (Suc i) k []
      | c # cs' \<Rightarrow> if c = i then True # wide_mask_at (Suc i) k cs'
                   else False # wide_mask_at (Suc i) k cs)"

definition wide_mask :: "nat \<Rightarrow> cols \<Rightarrow> bool list" where
  "wide_mask n cs = wide_mask_at 0 n cs"

lemma length_wide_mask_at[simp]: "length (wide_mask_at i k cs) = k"
  by (induct i k cs rule: wide_mask_at.induct) (auto split: list.splits)

lemma length_wide_mask[simp]: "length (wide_mask n cs) = n"
  unfolding wide_mask_def by simp

lemma wide_mask_at_eq:
  "sorted_wrt (<) cs \<Longrightarrow> \<forall>c \<in> set cs. i \<le> c \<Longrightarrow>
     wide_mask_at i k cs = map (\<lambda>j. (i + j) \<in> set cs) [0..<k]"
proof (induct i k cs rule: wide_mask_at.induct)
  case (2 i k cs)
  note IH_nil = 2(1) and IH_eq = 2(2) and IH_ne = 2(3) and srt = 2(4) and bnd = 2(5)
  show ?case
  proof (cases cs)
    case Nil
    with IH_nil srt bnd show ?thesis by (simp add: map_upt_Suc del: upt_Suc)
  next
    case (Cons c cs')
    show ?thesis
    proof (cases "c = i")
      case True
      have s': "sorted_wrt (<) cs'" using srt Cons by simp
      have b': "\<forall>d \<in> set cs'. Suc i \<le> d" using srt Cons True by force
      show ?thesis using IH_eq[OF Cons True s' b'] Cons True
        by (auto simp: map_upt_Suc simp del: upt_Suc)
    next
      case False
      have b': "\<forall>d \<in> set cs. Suc i \<le> d" using srt bnd Cons False by fastforce
      show ?thesis using IH_ne[OF Cons False srt b'] Cons False bnd srt
        by (auto simp: map_upt_Suc simp del: upt_Suc)
    qed
  qed
qed simp
lemma wide_mask_eq_join_mask:
  "sorted_wrt (<) cs \<Longrightarrow> wide_mask n cs = join_mask n (set cs)"
  unfolding wide_mask_def join_mask_def by (subst wide_mask_at_eq) auto

lemma length_dproj: "length bs = length xs \<Longrightarrow> length (dproj bs xs) = length (filter id bs)"
  by (induct bs xs rule: dproj.induct) auto

lemma dwiden_dproj:
  "length bs = length xs \<Longrightarrow> (\<And>i. i < length bs \<Longrightarrow> \<not> bs ! i \<Longrightarrow> xs ! i = None) \<Longrightarrow>
     dwiden bs (dproj bs xs) = xs"
proof (induct bs xs rule: dproj.induct)
  case (2 bs x xs)
  have "\<And>i. i < length bs \<Longrightarrow> \<not> bs ! i \<Longrightarrow> xs ! i = None"
    using 2(3)[of "Suc _"] by simp
  then show ?case using 2 by simp
next
  case (3 bs x xs)
  have "\<And>i. i < length bs \<Longrightarrow> \<not> bs ! i \<Longrightarrow> xs ! i = None"
    using 3(3)[of "Suc _"] by simp
  moreover have "x = None" using 3(3)[of 0] by simp
  ultimately show ?case using 3 by simp
qed simp_all

subsection \<open>The representation relation\<close>

lemma dwiden_dproj_wf: "wf_tuple n A x \<Longrightarrow> dwiden (join_mask n A) (dproj (join_mask n A) x) = x"
  by (rule dwiden_dproj) (auto simp: wf_tuple_def join_mask_def)

lemma inj_on_dproj_wf: "inj_on (dproj (join_mask n A)) {x. wf_tuple n A x}"
  by (rule inj_onI) (metis dwiden_dproj_wf mem_Collect_eq)

definition dtab :: "nat \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "dtab n A T = dproj (join_mask n A) ` T"

lemma dwiden_dtab: "table n A T \<Longrightarrow> dwiden (join_mask n A) ` dtab n A T = T"
  unfolding dtab_def table_def image_image
  by (auto simp: dwiden_dproj_wf intro!: rev_image_eqI)

lemma dtab_inj: "table n A T \<Longrightarrow> table n A T' \<Longrightarrow> dtab n A T = dtab n A T' \<Longrightarrow> T = T'"
  by (metis dwiden_dtab)

lemma dtab_in_iff: "table n A T \<Longrightarrow> wf_tuple n A x \<Longrightarrow> (dproj (join_mask n A) x \<in> dtab n A T) = (x \<in> T)"
  unfolding dtab_def table_def
  using inj_on_dproj_wf[of n A] by (auto simp: inj_on_def)
subsection \<open>A short tuple is the wide one read at its columns\<close>

lemma nth_Cons_shift: "i < d \<Longrightarrow> (z # zs) ! (d - i) = zs ! (d - Suc i)"
  by (metis Suc_diff_Suc nth_Cons_Suc)

lemma dproj_wide_mask_at:
  "sorted_wrt (<) cs \<Longrightarrow> \<forall>c \<in> set cs. i \<le> c \<and> c < i + k \<Longrightarrow> length xs = k \<Longrightarrow>
     dproj (wide_mask_at i k cs) xs = map (\<lambda>c. xs ! (c - i)) cs"
proof (induct i k cs arbitrary: xs rule: wide_mask_at.induct)
  case (2 i k cs)
  note IH_nil = 2(1) and IH_eq = 2(2) and IH_ne = 2(3)
  note srt = 2(4) and bnd = 2(5) and len = 2(6)
  obtain z zs where xs: "xs = z # zs" and lzs: "length zs = k"
    using len by (cases xs) auto
  show ?case
  proof (cases cs)
    case Nil
    with IH_nil srt bnd lzs xs show ?thesis by simp
  next
    case (Cons c cs')
    show ?thesis
    proof (cases "c = i")
      case True
      have s': "sorted_wrt (<) cs'" using srt Cons by simp
      have b': "\<forall>d \<in> set cs'. Suc i \<le> d \<and> d < Suc i + k" using srt bnd Cons True by force
      have sh: "\<And>d. d \<in> set cs' \<Longrightarrow> (z # zs) ! (d - i) = zs ! (d - Suc i)"
        using b' by (auto intro!: nth_Cons_shift)
      show ?thesis using IH_eq[OF Cons True s' b' lzs] Cons True xs sh by simp
    next
      case False
      have b': "\<forall>d \<in> set cs. Suc i \<le> d \<and> d < Suc i + k"
        using srt bnd Cons False by fastforce
      have sh: "\<And>d. d \<in> set cs \<Longrightarrow> (z # zs) ! (d - i) = zs ! (d - Suc i)"
        using b' by (auto intro!: nth_Cons_shift)
      show ?thesis using IH_ne[OF Cons False srt b' lzs] Cons False xs sh by simp
    qed
  qed
next
  case (1 i cs xs)
  then show ?case by (cases cs) auto
qed

lemma dproj_wide_mask_eq_map_nth:
  "sorted_wrt (<) cs \<Longrightarrow> \<forall>c \<in> set cs. c < n \<Longrightarrow> length xs = n \<Longrightarrow>
     dproj (wide_mask n cs) xs = map (\<lambda>c. xs ! c) cs"
  unfolding wide_mask_def by (subst dproj_wide_mask_at) auto

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

fun djoin1 :: "mrg list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple option" where
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

lemma join1_Some_length: "join1 (x, y) = Some v \<Longrightarrow> length v = length x"
  by (induct "(x, y)" arbitrary: x y v rule: join1.induct) (auto split: if_splits)

lemma join1_nth:
  "join1 (x, y) = Some v \<Longrightarrow> i < length v \<Longrightarrow>
     v ! i = (if x ! i = None then y ! i else x ! i)"
proof (induct "(x, y)" arbitrary: x y v i rule: join1.induct)
  case (2 xs ys)
  then show ?case by (cases i) auto
next
  case (3 x xs ys)
  then show ?case by (cases i) auto
next
  case (4 xs y ys)
  then show ?case by (cases i) auto
next
  case (5 x xs y ys)
  then show ?case by (cases i) (auto split: if_splits)
qed auto

lemma djoin1_join1:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and b1: "\<forall>c \<in> set cs1. c < n" and b2: "\<forall>c \<in> set cs2. c < n"
    and w1: "wf_tuple n (set cs1) x" and w2: "wf_tuple n (set cs2) y"
  shows "djoin1 (mrg_plan cs1 cs2) (dproj (wide_mask n cs1) x) (dproj (wide_mask n cs2) y)
       = map_option (dproj (wide_mask n (merge_cols cs1 cs2))) (join1 (x, y))"
proof -
  have lx: "length x = n" and ly: "length y = n"
    using w1 w2 by (auto simp: wf_tuple_def)
  have xN: "\<And>i. i < n \<Longrightarrow> i \<notin> set cs1 \<Longrightarrow> x ! i = None"
    and xS: "\<And>i. i < n \<Longrightarrow> i \<in> set cs1 \<Longrightarrow> x ! i \<noteq> None"
    using w1 by (auto simp: wf_tuple_def)
  have yN: "\<And>i. i < n \<Longrightarrow> i \<notin> set cs2 \<Longrightarrow> y ! i = None"
    and yS: "\<And>i. i < n \<Longrightarrow> i \<in> set cs2 \<Longrightarrow> y ! i \<noteq> None"
    using w2 by (auto simp: wf_tuple_def)
  have srt: "sorted_wrt (<) (merge_cols cs1 cs2)"
    using s1 s2 by (induct cs1 cs2 rule: merge_cols.induct) (auto simp: set_merge_cols)
  have bnd: "\<forall>c \<in> set (merge_cols cs1 cs2). c < n"
    using b1 b2 by (auto simp: set_merge_cols)
  have agree: "(\<exists>v. join1 (x, y) = Some v) \<longleftrightarrow> (\<forall>c \<in> set cs1 \<inter> set cs2. x ! c = y ! c)"
  proof
    assume "\<exists>v. join1 (x, y) = Some v"
    then have *: "\<forall>i<length x. (x ! i = None \<or> y ! i = None) \<or>
        (\<exists>a. x ! i = Some a \<and> y ! i = Some a)"
      unfolding join1_Some_iff by simp
    show "\<forall>c \<in> set cs1 \<inter> set cs2. x ! c = y ! c"
    proof
      fix c assume c: "c \<in> set cs1 \<inter> set cs2"
      then have cn: "c < n" using b1 by auto
      show "x ! c = y ! c"
        using *[rule_format, of c] cn lx xS[OF cn] yS[OF cn] c by auto
    qed
  next
    assume *: "\<forall>c \<in> set cs1 \<inter> set cs2. x ! c = y ! c"
    have "\<forall>i<length x. (x ! i = None \<or> y ! i = None) \<or>
        (\<exists>a. x ! i = Some a \<and> y ! i = Some a)"
    proof (intro allI impI)
      fix i assume "i < length x"
      then have i: "i < n" using lx by simp
      show "(x ! i = None \<or> y ! i = None) \<or> (\<exists>a. x ! i = Some a \<and> y ! i = Some a)"
      proof (cases "i \<in> set cs1 \<and> i \<in> set cs2")
        case True
        then have "x ! i = y ! i" using * by auto
        moreover obtain a where "x ! i = Some a" using xS[OF i] True by auto
        ultimately show ?thesis by auto
      next
        case False
        then show ?thesis using xN[OF i] yN[OF i] by auto
      qed
    qed
    then show "\<exists>v. join1 (x, y) = Some v"
      unfolding join1_Some_iff using lx ly by simp
  qed
  show ?thesis
  proof (cases "join1 (x, y)")
    case None
    then have "\<not> (\<forall>c \<in> set cs1 \<inter> set cs2. x ! c = y ! c)" using agree by auto
    then show ?thesis
      using None s1 s2 b1 b2 lx ly
      by (simp add: dproj_wide_mask_eq_map_nth djoin1_mrg_plan)
  next
    case (Some v)
    then have ag: "\<forall>c \<in> set cs1 \<inter> set cs2. x ! c = y ! c" using agree by auto
    have lv: "length v = n" using Some join1_Some_length lx by metis
    have "map (\<lambda>c. if c \<in> set cs1 then x ! c else y ! c) (merge_cols cs1 cs2)
        = map (\<lambda>c. v ! c) (merge_cols cs1 cs2)"
    proof (intro map_cong refl)
      fix c assume c: "c \<in> set (merge_cols cs1 cs2)"
      then have cn: "c < n" using bnd by auto
      show "(if c \<in> set cs1 then x ! c else y ! c) = v ! c"
      proof (cases "c \<in> set cs1")
        case True
        then have "x ! c \<noteq> None" using xS[OF cn] by auto
        then show ?thesis using join1_nth[OF Some, of c] lv cn True by auto
      next
        case False
        then have "x ! c = None" using xN[OF cn] by auto
        then show ?thesis using join1_nth[OF Some, of c] lv cn False by auto
      qed
    qed
    then show ?thesis
      using Some ag s1 s2 b1 b2 lx ly lv srt bnd
      by (simp add: dproj_wide_mask_eq_map_nth djoin1_mrg_plan)
  qed
qed

subsection \<open>Tables of short tuples\<close>

definition dtabc :: "nat \<Rightarrow> cols \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "dtabc n cs T = dproj (wide_mask n cs) ` T"

lemma dtabc_eq_dtab: "sorted_wrt (<) cs \<Longrightarrow> dtabc n cs T = dtab n (set cs) T"
  by (simp add: dtabc_def dtab_def wide_mask_eq_join_mask)

lemma sorted_merge_cols:
  "sorted_wrt (<) cs \<Longrightarrow> sorted_wrt (<) ds \<Longrightarrow> sorted_wrt (<) (merge_cols cs ds)"
  by (induct cs ds rule: merge_cols.induct) (auto simp: set_merge_cols)

text \<open>The short join of two tables is the short form of the kernel's join of the wide ones.\<close>

lemma dtabc_join:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and b1: "\<forall>c \<in> set cs1. c < n" and b2: "\<forall>c \<in> set cs2. c < n"
    and t1: "table n (set cs1) T" and t2: "table n (set cs2) T'"
  shows "dtabc n (merge_cols cs1 cs2) (join T True T')
       = (\<Union>a \<in> dtabc n cs1 T. \<Union>b \<in> dtabc n cs2 T'.
            set_option (djoin1 (mrg_plan cs1 cs2) a b))"
proof -
  have key: "\<And>a b. a \<in> T \<Longrightarrow> b \<in> T' \<Longrightarrow>
      djoin1 (mrg_plan cs1 cs2) (dproj (wide_mask n cs1) a) (dproj (wide_mask n cs2) b)
        = map_option (dproj (wide_mask n (merge_cols cs1 cs2))) (join1 (a, b))"
    using t1 t2 by (intro djoin1_join1[OF s1 s2 b1 b2]) (auto simp: table_def)
  have "dtabc n (merge_cols cs1 cs2) (join T True T')
      = (\<Union>a \<in> T. \<Union>b \<in> T'. dproj (wide_mask n (merge_cols cs1 cs2)) ` set_option (join1 (a, b)))"
    unfolding dtabc_def join_True_code by blast
  also have "\<dots> = (\<Union>a \<in> T. \<Union>b \<in> T'. set_option
      (djoin1 (mrg_plan cs1 cs2) (dproj (wide_mask n cs1) a) (dproj (wide_mask n cs2) b)))"
    by (intro SUP_cong refl) (auto simp: key split: option.splits)
  also have "\<dots> = (\<Union>a \<in> dtabc n cs1 T. \<Union>b \<in> dtabc n cs2 T'.
      set_option (djoin1 (mrg_plan cs1 cs2) a b))"
    unfolding dtabc_def by blast
  finally show ?thesis .
qed

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
  the kernel's masked projection.\<close>

lemma dproj_left_key_eq:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and sub: "set cs2 \<subseteq> set cs1" and b1: "\<forall>c \<in> set cs1. c < n"
    and w: "wf_tuple n (set cs1) a"
  shows "dproj (mrg_left_key (mrg_plan cs1 cs2)) (dproj (wide_mask n cs1) a)
       = dproj (wide_mask n cs2) (proj_tuple (join_mask n (set cs2)) a)"
proof -
  have la: "length a = n" using w by (simp add: wf_tuple_def)
  have b2: "\<forall>c \<in> set cs2. c < n" using sub b1 by auto
  have lp: "length (proj_tuple (join_mask n (set cs2)) a) = n"
    using la by (simp add: proj_tuple_alt join_mask_def)
  have "\<And>c. c \<in> set cs2 \<Longrightarrow> proj_tuple (join_mask n (set cs2)) a ! c = a ! c"
    using la b2 by (auto simp: proj_tuple_alt join_mask_def)
  then show ?thesis
    using dproj_mrg_left_key[OF s1 s2 sub, of "\<lambda>c. a ! c"]
      dproj_wide_mask_eq_map_nth[OF s1 b1 la]
      dproj_wide_mask_eq_map_nth[OF s2 b2 lp]
    by (simp cong: map_cong)
qed

subsection \<open>The join when one operand's columns are among the other's\<close>

definition dsemi :: "bool list \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "dsemi msk pos A B = Set.filter (\<lambda>a. (dproj msk a \<in> B) = pos) A"

lemma wf_tuple_proj_tuple:
  "wf_tuple n X a \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> wf_tuple n Y (proj_tuple (join_mask n Y) a)"
  by (auto simp: wf_tuple_def proj_tuple_alt join_mask_def)

lemma join_cond_eq: "join_cond pos t v = ((v \<in> t) = pos)"
  by (cases pos) auto

text \<open>
  This is the shape the anti-join of @{text "\<phi> AND NOT \<psi>"} takes, and the intersection when the
  two column lists are equal: every tuple of the left operand either has a partner or does not,
  and the test is a membership of its projection.
\<close>

theorem dsemi_join:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and sub: "set cs2 \<subseteq> set cs1" and b1: "\<forall>c \<in> set cs1. c < n"
    and t1: "table n (set cs1) T" and t2: "table n (set cs2) T'"
  shows "dsemi (mrg_left_key (mrg_plan cs1 cs2)) pos (dtabc n cs1 T) (dtabc n cs2 T')
       = dtabc n cs1 (join T pos T')"
proof -
  have b2: "\<forall>c \<in> set cs2. c < n" using sub b1 by auto
  have "join T pos T' = {a \<in> T. (proj_tuple (join_mask n (set cs2)) a \<in> T') = pos}"
    using join_sub[OF sub t2 t1] by (simp add: proj_tuple_in_join_def join_cond_eq)
  moreover have "\<And>a. a \<in> T \<Longrightarrow>
      (dproj (mrg_left_key (mrg_plan cs1 cs2)) (dproj (wide_mask n cs1) a) \<in> dtabc n cs2 T')
        = (proj_tuple (join_mask n (set cs2)) a \<in> T')"
  proof -
    fix a assume a: "a \<in> T"
    then have w: "wf_tuple n (set cs1) a" using t1 by (simp add: table_def)
    have wp: "wf_tuple n (set cs2) (proj_tuple (join_mask n (set cs2)) a)"
      using wf_tuple_proj_tuple[OF w sub] .
    show "(dproj (mrg_left_key (mrg_plan cs1 cs2)) (dproj (wide_mask n cs1) a) \<in> dtabc n cs2 T')
        = (proj_tuple (join_mask n (set cs2)) a \<in> T')"
      unfolding dproj_left_key_eq[OF s1 s2 sub b1 w] dtabc_eq_dtab[OF s2]
      by (subst wide_mask_eq_join_mask[OF s2], rule dtab_in_iff[OF t2 wp])
  qed
  ultimately show ?thesis
    unfolding dsemi_def dtabc_def by auto
qed

subsection \<open>The short form of a table commutes with intersection and difference\<close>

lemma dtabc_Int:
  assumes s: "sorted_wrt (<) cs" and t1: "table n (set cs) T" and t2: "table n (set cs) T'"
  shows "dtabc n cs (T \<inter> T') = dtabc n cs T \<inter> dtabc n cs T'"
proof (intro equalityI subsetI)
  fix z assume "z \<in> dtabc n cs T \<inter> dtabc n cs T'"
  then obtain a a' where a: "a \<in> T" "z = dproj (wide_mask n cs) a"
    and a': "a' \<in> T'" "z = dproj (wide_mask n cs) a'"
    unfolding dtabc_def by auto
  have "a = a'" using a a' t1 t2 inj_on_dproj_wf[of n "set cs"]
    by (auto simp: table_def wide_mask_eq_join_mask[OF s] inj_on_def)
  then show "z \<in> dtabc n cs (T \<inter> T')" using a a' unfolding dtabc_def by auto
qed (auto simp: dtabc_def)

lemma dtabc_Diff:
  assumes s: "sorted_wrt (<) cs" and t1: "table n (set cs) T" and t2: "table n (set cs) T'"
  shows "dtabc n cs (T - T') = dtabc n cs T - dtabc n cs T'"
proof (intro equalityI subsetI)
  fix z assume "z \<in> dtabc n cs (T - T')"
  then obtain a where a: "a \<in> T" "a \<notin> T'" "z = dproj (wide_mask n cs) a"
    unfolding dtabc_def by auto
  have "z \<notin> dtabc n cs T'"
  proof
    assume "z \<in> dtabc n cs T'"
    then obtain a' where a': "a' \<in> T'" "z = dproj (wide_mask n cs) a'"
      unfolding dtabc_def by auto
    have "a = a'" using a a' t1 t2 inj_on_dproj_wf[of n "set cs"]
      by (auto simp: table_def wide_mask_eq_join_mask[OF s] inj_on_def)
    then show False using a a' by auto
  qed
  then show "z \<in> dtabc n cs T - dtabc n cs T'" using a unfolding dtabc_def by auto
qed (auto simp: dtabc_def)

subsection \<open>Equal columns, and a right operand with no columns\<close>

theorem dtabc_join_eq:
  assumes s: "sorted_wrt (<) cs" and t1: "table n (set cs) T" and t2: "table n (set cs) T'"
  shows "(if pos then dtabc n cs T \<inter> dtabc n cs T' else dtabc n cs T - dtabc n cs T')
       = dtabc n cs (join T pos T')"
  using join_eq[OF t2 t1, of pos] dtabc_Int[OF s t1 t2] dtabc_Diff[OF s t1 t2] by simp

lemma wf_tuple_empty_cols: "wf_tuple n {} x \<longleftrightarrow> x = replicate n None"
  by (auto simp: wf_tuple_def intro!: nth_equalityI)

lemma wide_mask_at_Nil: "wide_mask_at i k [] = replicate k False"
  by (induct i k "[] :: cols" rule: wide_mask_at.induct) auto

lemma wide_mask_Nil: "wide_mask n [] = replicate n False"
  unfolding wide_mask_def by (rule wide_mask_at_Nil)

lemma dproj_replicate_False: "length xs = k \<Longrightarrow> dproj (replicate k False) xs = []"
  by (induct xs arbitrary: k) auto

lemma dtabc_Nil_cols:
  assumes "table n {} T'"
  shows "dtabc n [] T' = (if T' = {} then {} else {[]})"
proof -
  have "\<And>x. x \<in> T' \<Longrightarrow> dproj (wide_mask n []) x = []"
    using assms by (auto simp: table_def wf_tuple_def wide_mask_Nil dproj_replicate_False)
  then show ?thesis unfolding dtabc_def by auto
qed

theorem dtabc_join_no_cols:
  assumes t1: "table n (set cs) T" and t2: "table n {} T'"
  shows "(if pos = ([] \<in> dtabc n [] T') then dtabc n cs T else {})
       = dtabc n cs (join T pos T')"
proof -
  have "([] \<in> dtabc n [] T') = (replicate n None \<in> T')"
    using t2 by (auto simp: dtabc_Nil_cols table_def wf_tuple_empty_cols)
  then show ?thesis
    using join_no_cols[OF t2 t1, of pos] by (simp add: dtabc_def)
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
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and sub: "set cs1 \<subseteq> set cs2" and b2: "\<forall>c \<in> set cs2. c < n"
    and w: "wf_tuple n (set cs2) b"
  shows "dproj (mrg_right_key (mrg_plan cs1 cs2)) (dproj (wide_mask n cs2) b)
       = dproj (wide_mask n cs1) (proj_tuple (join_mask n (set cs1)) b)"
proof -
  have lb: "length b = n" using w by (simp add: wf_tuple_def)
  have b1: "\<forall>c \<in> set cs1. c < n" using sub b2 by auto
  have lp: "length (proj_tuple (join_mask n (set cs1)) b) = n"
    using lb by (simp add: proj_tuple_alt join_mask_def)
  have "\<And>c. c \<in> set cs1 \<Longrightarrow> proj_tuple (join_mask n (set cs1)) b ! c = b ! c"
    using lb b1 by (auto simp: proj_tuple_alt join_mask_def)
  then show ?thesis
    using dproj_mrg_right_key[OF s1 s2 sub, of "\<lambda>c. b ! c"]
      dproj_wide_mask_eq_map_nth[OF s2 b2 lb]
      dproj_wide_mask_eq_map_nth[OF s1 b1 lp]
    by (simp cong: map_cong)
qed

theorem dsup_join:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and sub: "set cs1 \<subseteq> set cs2" and b2: "\<forall>c \<in> set cs2. c < n"
    and t1: "table n (set cs1) T" and t2: "table n (set cs2) T'"
  shows "Set.filter (\<lambda>b. dproj (mrg_right_key (mrg_plan cs1 cs2)) b \<in> dtabc n cs1 T)
           (dtabc n cs2 T')
       = dtabc n cs2 (join T True T')"
proof -
  have b1: "\<forall>c \<in> set cs1. c < n" using sub b2 by auto
  have "join T True T' = {b \<in> T'. (proj_tuple (join_mask n (set cs1)) b \<in> T) = True}"
    using join_sub'[OF sub t2 t1] by (simp add: proj_tuple_in_join_def join_cond_eq)
  moreover have "\<And>b. b \<in> T' \<Longrightarrow>
      (dproj (mrg_right_key (mrg_plan cs1 cs2)) (dproj (wide_mask n cs2) b) \<in> dtabc n cs1 T)
        = (proj_tuple (join_mask n (set cs1)) b \<in> T)"
  proof -
    fix b assume b: "b \<in> T'"
    then have w: "wf_tuple n (set cs2) b" using t2 by (simp add: table_def)
    have wp: "wf_tuple n (set cs1) (proj_tuple (join_mask n (set cs1)) b)"
      using wf_tuple_proj_tuple[OF w sub] .
    show "(dproj (mrg_right_key (mrg_plan cs1 cs2)) (dproj (wide_mask n cs2) b) \<in> dtabc n cs1 T)
        = (proj_tuple (join_mask n (set cs1)) b \<in> T)"
      unfolding dproj_right_key_eq[OF s1 s2 sub b2 w] dtabc_eq_dtab[OF s1]
      by (subst wide_mask_eq_join_mask[OF s1], rule dtab_in_iff[OF t1 wp])
  qed
  ultimately show ?thesis unfolding dtabc_def by auto
qed

subsection \<open>The general join: an index on the shared columns\<close>

text \<open>
  When neither operand's columns are contained in the other's, one side is indexed by the
  shared columns and the other probes the index.  A probe that hits knows the two tuples agree
  on the shared columns, so the merge needs no test at all.
\<close>

fun dmerge :: "mrg list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
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
  "dindex msk B = fold (dindex_step msk) (csorted_list_of_set B) Mapping.empty"

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

text \<open>The index is built on the smaller side and the larger one probes it, as in
  @{const bin_join}: indexing costs a lookup per tuple of the indexed side and probing one per
  tuple of the other, so indexing the larger side buys a big index that is read a few times.\<close>

definition dgen_join :: "mrg list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
    event_data table \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dgen_join p lk rk A B =
     (if card A \<le> card B
      then (let m = dindex lk A in fold (dprobe_step_l p rk m) (csorted_list_of_set B) empty_table)
      else (let m = dindex rk B in fold (dprobe_step p lk m) (csorted_list_of_set A) empty_table))"

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
  assumes "set (csorted_list_of_set B) = B"
  shows "set (bucket (dindex msk B) k) = {b \<in> B. dproj msk b = k}"
  using dindex_fold_lookup[of msk "csorted_list_of_set B" Mapping.empty k] assms
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
  assumes cA: "set (csorted_list_of_set A) = A" and cB: "set (csorted_list_of_set B) = B"
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

theorem dtabc_gen_join:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and b1: "\<forall>c \<in> set cs1. c < n" and b2: "\<forall>c \<in> set cs2. c < n"
    and t1: "table n (set cs1) T" and t2: "table n (set cs2) T'"
    and fT: "finite T" and fT': "finite T'"
  shows "dgen_join (mrg_plan cs1 cs2) (mrg_left_key (mrg_plan cs1 cs2))
           (mrg_right_key (mrg_plan cs1 cs2)) (dtabc n cs1 T) (dtabc n cs2 T')
       = dtabc n (merge_cols cs1 cs2) (join T True T')"
proof -
  let ?p = "mrg_plan cs1 cs2"
  have cA: "set (csorted_list_of_set (dtabc n cs1 T)) = dtabc n cs1 T"
    and cB: "set (csorted_list_of_set (dtabc n cs2 T')) = dtabc n cs2 T'"
    using fT fT' by (auto simp: dtabc_def intro!: set_csorted_list_of_set_etuple)
  have la: "\<And>a. a \<in> dtabc n cs1 T \<Longrightarrow> length a = length (filter (\<lambda>m. m \<noteq> MRgt) ?p)"
    using t1 by (auto simp: dtabc_def table_def wf_tuple_def length_filter_mrg_plan_left
        dproj_wide_mask_eq_map_nth[OF s1 b1])
  have lb: "\<And>b. b \<in> dtabc n cs2 T' \<Longrightarrow> length b = length (filter (\<lambda>m. m \<noteq> MLft) ?p)"
    using t2 by (auto simp: dtabc_def table_def wf_tuple_def length_filter_mrg_plan_right
        dproj_wide_mask_eq_map_nth[OF s2 b2])
  have "dgen_join ?p (mrg_left_key ?p) (mrg_right_key ?p) (dtabc n cs1 T) (dtabc n cs2 T')
      = (\<Union>a \<in> dtabc n cs1 T. \<Union>b \<in> dtabc n cs2 T'. set_option (djoin1 ?p a b))"
    unfolding dgen_join_eq[OF cA cB]
    by (auto simp: set_option_djoin1[OF la lb] split: if_splits)
  also have "\<dots> = dtabc n (merge_cols cs1 cs2) (join T True T')"
    by (rule dtabc_join[OF s1 s2 b1 b2 t1 t2, symmetric])
  finally show ?thesis .
qed

subsection \<open>Dispatching on the shape of the two column lists\<close>

text \<open>
  The plan is computed once, when the formula is compiled, and replayed at every time point;
  the kernel's @{const bin_join} recomputes the same case distinction from the two variable
  sets on every call.
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

lemma sorted_wrt_less_unique:
  "sorted_wrt (<) xs \<Longrightarrow> sorted_wrt (<) ys \<Longrightarrow> set xs = set ys \<Longrightarrow> xs = (ys :: 'a :: linorder list)"
  by (simp add: strict_sorted_iff sorted_distinct_set_unique)

lemma merge_cols_sub_left:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     merge_cols cs1 cs2 = cs1"
  by (rule sorted_wrt_less_unique[OF sorted_merge_cols]) (auto simp: set_merge_cols)

lemma merge_cols_sub_right:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs1 \<subseteq> set cs2 \<Longrightarrow>
     merge_cols cs1 cs2 = cs2"
  by (rule sorted_wrt_less_unique[OF sorted_merge_cols]) (auto simp: set_merge_cols)

lemma dtabc_empty_iff: "(dtabc n cs T = {}) = (T = {})"
  by (auto simp: dtabc_def)

text \<open>Every shape of the plan computes the short form of the kernel's join.  A negative join
  needs the right operand's columns among the left's, which is what the safety condition of
  @{term "\<phi> AND NOT \<psi>"} provides; the other shapes then arise only for a positive join.\<close>

theorem dbin_join0_join:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and b1: "\<forall>c \<in> set cs1. c < n" and b2: "\<forall>c \<in> set cs2. c < n"
    and t1: "table n (set cs1) T" and t2: "table n (set cs2) T'"
    and neg: "\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1"
    and fT: "finite T" and fT': "finite T'"
  shows "dbin_join0 (mk_djoin cs1 cs2) (dtabc n cs1 T) pos (dtabc n cs2 T')
       = dtabc n (merge_cols cs1 cs2) (join T pos T')"
proof (cases "cs1 = cs2")
  case True
  have "dbin_join0 (mk_djoin cs1 cs2) (dtabc n cs1 T) pos (dtabc n cs2 T')
      = (if pos then dtabc n cs1 T \<inter> dtabc n cs1 T' else dtabc n cs1 T - dtabc n cs1 T')"
    using True by (simp add: mk_djoin_def)
  also have "\<dots> = dtabc n cs1 (join T pos T')"
    using True t2 by (intro dtabc_join_eq[OF s1 t1]) simp
  finally show ?thesis using True merge_cols_sub_left[OF s1 s2] by simp
next
  case ne: False
  show ?thesis
  proof (cases "cs2 = []")
    case True
    then have tt: "table n {} T'" using t2 by simp
    have "dbin_join0 (mk_djoin cs1 cs2) (dtabc n cs1 T) pos (dtabc n cs2 T')
        = (if pos = ([] \<in> dtabc n [] T') then dtabc n cs1 T else {})"
      using ne True by (simp add: mk_djoin_def empty_table_def)
    also have "\<dots> = dtabc n cs1 (join T pos T')" by (rule dtabc_join_no_cols[OF t1 tt])
    finally show ?thesis using True by (simp add: merge_cols_Nil2)
  next
    case ne2: False
    let ?p = "mrg_plan cs1 cs2"
    show ?thesis
    proof (cases "no_right ?p")
      case True
      then have sub: "set cs2 \<subseteq> set cs1" using no_right_mrg_plan[OF s1 s2] by simp
      show ?thesis using dsemi_join[OF s1 s2 sub b1 t1 t2, of pos]
          merge_cols_sub_left[OF s1 s2 sub] ne ne2 True
        by (simp add: mk_djoin_def)
    next
      case nr: False
      then have nsub: "\<not> set cs2 \<subseteq> set cs1" using no_right_mrg_plan[OF s1 s2] by simp
      then have p: "pos" using neg by blast
      show ?thesis
      proof (cases "no_left ?p")
        case True
        then have sub: "set cs1 \<subseteq> set cs2" using no_left_mrg_plan[OF s1 s2] by simp
        show ?thesis using dsup_join[OF s1 s2 sub b2 t1 t2]
            merge_cols_sub_right[OF s1 s2 sub] ne ne2 nr True p
          by (simp add: mk_djoin_def)
      next
        case False
        show ?thesis using dtabc_gen_join[OF s1 s2 b1 b2 t1 t2 fT fT']
            ne ne2 nr False p
          by (simp add: mk_djoin_def Let_def)
      qed
    qed
  qed
qed

theorem dbin_join_join:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and b1: "\<forall>c \<in> set cs1. c < n" and b2: "\<forall>c \<in> set cs2. c < n"
    and t1: "table n (set cs1) T" and t2: "table n (set cs2) T'"
    and neg: "\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1"
    and fT: "finite T" and fT': "finite T'"
  shows "dbin_join (mk_djoin cs1 cs2) (dtabc n cs1 T) pos (dtabc n cs2 T')
       = dtabc n (merge_cols cs1 cs2) (join T pos T')"
proof (cases "T = {}")
  case True
  then show ?thesis
    by (simp add: dbin_join_def dtabc_empty_iff join_empty_left empty_table_def dtabc_def)
next
  case T: False
  show ?thesis
  proof (cases "T' = {}")
    case True
    then show ?thesis using T neg merge_cols_sub_left[OF s1 s2]
      by (cases pos)
        (simp_all add: dbin_join_def dtabc_empty_iff join_empty_right empty_table_def dtabc_def)
  next
    case False
    then show ?thesis using T
      by (simp add: dbin_join_def dtabc_empty_iff
          dbin_join0_join[OF s1 s2 b1 b2 t1 t2 neg fT fT'])
  qed
qed

text \<open>And hence the short join refines the kernel's @{const bin_join}.\<close>

corollary dbin_join_bin_join:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and b1: "\<forall>c \<in> set cs1. c < n" and b2: "\<forall>c \<in> set cs2. c < n"
    and t1: "table n (set cs1) T" and t2: "table n (set cs2) T'"
    and neg: "\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1"
    and fT: "finite T" and fT': "finite T'"
  shows "dbin_join (mk_djoin cs1 cs2) (dtabc n cs1 T) pos (dtabc n cs2 T')
       = dtabc n (merge_cols cs1 cs2) (bin_join n (set cs1) T pos (set cs2) T')"
  unfolding bin_join_table[OF t1 t2]
  by (rule dbin_join_join[OF s1 s2 b1 b2 t1 t2 neg fT fT'])

subsection \<open>The multi-way join\<close>

text \<open>
  The kernel's @{const mmulti_join'} picks an order at run time from the variable sets; the
  dense evaluator joins left to right against a plan list computed once.  The two agree: the
  kernel's own optimisation lemmas say that merging two adjacent positive operands into their
  join, or removing a negative operand by an anti-join, leaves the result unchanged.
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

fun kands_pos :: "'a table \<Rightarrow> 'a table list \<Rightarrow> 'a table" where
  "kands_pos t [] = t"
| "kands_pos t (u # us) = kands_pos (join t True u) us"

fun kands_neg :: "'a table \<Rightarrow> 'a table list \<Rightarrow> 'a table" where
  "kands_neg t [] = t"
| "kands_neg t (u # us) = kands_neg (join t False u) us"

lemma finite_these: "finite A \<Longrightarrow> finite (Option.these A)"
  by (simp add: Option.these_def)

lemma finite_join: "finite X \<Longrightarrow> finite Y \<Longrightarrow> finite (join X b Y)"
  by (cases b) (auto simp: join_True_code join_False_alt)

lemma set_dands_cols: "set (dands_cols acc css) = set acc \<union> (\<Union>c \<in> set css. set c)"
  by (induct css arbitrary: acc) (auto simp: set_merge_cols)

lemma sorted_dands_cols:
  "sorted_wrt (<) acc \<Longrightarrow> \<forall>c \<in> set css. sorted_wrt (<) c \<Longrightarrow> sorted_wrt (<) (dands_cols acc css)"
  by (induct css arbitrary: acc) (auto simp: sorted_merge_cols)

abbreviation (input) wf_operand :: "nat \<Rightarrow> cols \<Rightarrow> event_data table \<Rightarrow> bool" where
  "wf_operand n c U \<equiv> sorted_wrt (<) c \<and> (\<forall>d \<in> set c. d < n) \<and> table n (set c) U \<and> finite U"

theorem dands_pos_dtabc:
  assumes "sorted_wrt (<) acc" and "\<forall>c \<in> set acc. c < n"
    and "table n (set acc) T" and "finite T"
    and "list_all2 (wf_operand n) css Us"
  shows "dands_pos (dands_plans acc css) (dtabc n acc T) (map2 (dtabc n) css Us)
       = dtabc n (dands_cols acc css) (kands_pos T Us)"
  using assms
proof (induct css arbitrary: acc T Us)
  case (Cons c cs)
  from Cons(6) obtain U Us' where U: "Us = U # Us'" and wf: "wf_operand n c U"
    and rest: "list_all2 (wf_operand n) cs Us'"
    by (cases Us) auto
  have j: "dbin_join (mk_djoin acc c) (dtabc n acc T) True (dtabc n c U)
      = dtabc n (merge_cols acc c) (join T True U)"
  proof (rule dbin_join_join)
    show "sorted_wrt (<) acc" by (rule Cons(2))
    show "sorted_wrt (<) c" using wf by simp
    show "\<forall>d \<in> set acc. d < n" by (rule Cons(3))
    show "\<forall>d \<in> set c. d < n" using wf by simp
    show "table n (set acc) T" by (rule Cons(4))
    show "table n (set c) U" using wf by simp
    show "\<not> True \<Longrightarrow> set c \<subseteq> set acc" by simp
    show "finite T" by (rule Cons(5))
    show "finite U" using wf by simp
  qed
  have t: "table n (set (merge_cols acc c)) (join T True U)"
    using Cons(4) wf by (auto simp: set_merge_cols
        intro!: join_table[of n "set acc" T "set c" U True])
  have "dands_pos (dands_plans acc (c # cs)) (dtabc n acc T) (map2 (dtabc n) (c # cs) Us)
      = dands_pos (dands_plans (merge_cols acc c) cs)
          (dtabc n (merge_cols acc c) (join T True U)) (map2 (dtabc n) cs Us')"
    unfolding U by (simp add: j)
  also have "\<dots> = dtabc n (dands_cols (merge_cols acc c) cs) (kands_pos (join T True U) Us')"
  proof (rule Cons(1))
    show "sorted_wrt (<) (merge_cols acc c)" using Cons(2) wf by (simp add: sorted_merge_cols)
    show "\<forall>d \<in> set (merge_cols acc c). d < n" using Cons(3) wf by (auto simp: set_merge_cols)
    show "table n (set (merge_cols acc c)) (join T True U)" by (rule t)
    show "finite (join T True U)" using Cons(5) wf by (simp add: finite_join)
    show "list_all2 (wf_operand n) cs Us'" by (rule rest)
  qed
  finally show ?case unfolding U by simp
qed simp

theorem dands_neg_dtabc:
  assumes "sorted_wrt (<) acc" and "\<forall>c \<in> set acc. c < n"
    and "table n (set acc) T" and "finite T"
    and "list_all2 (wf_operand n) nss Vs" and "\<forall>c \<in> set nss. set c \<subseteq> set acc"
  shows "dands_neg (dands_plans acc nss) (dtabc n acc T) (map2 (dtabc n) nss Vs)
       = dtabc n acc (kands_neg T Vs)"
  using assms
proof (induct nss arbitrary: acc T Vs)
  case (Cons c cs)
  from Cons(6) obtain V Vs' where V: "Vs = V # Vs'" and wf: "wf_operand n c V"
    and rest: "list_all2 (wf_operand n) cs Vs'"
    by (cases Vs) auto
  have sub: "set c \<subseteq> set acc" using Cons(7) by simp
  have mc: "merge_cols acc c = acc"
    using Cons(2) wf sub by (simp add: merge_cols_sub_left)
  have j0: "dbin_join (mk_djoin acc c) (dtabc n acc T) False (dtabc n c V)
      = dtabc n (merge_cols acc c) (join T False V)"
  proof (rule dbin_join_join)
    show "sorted_wrt (<) acc" by (rule Cons(2))
    show "sorted_wrt (<) c" using wf by simp
    show "\<forall>d \<in> set acc. d < n" by (rule Cons(3))
    show "\<forall>d \<in> set c. d < n" using wf by simp
    show "table n (set acc) T" by (rule Cons(4))
    show "table n (set c) V" using wf by simp
    show "\<not> False \<Longrightarrow> set c \<subseteq> set acc" by (rule sub)
    show "finite T" by (rule Cons(5))
    show "finite V" using wf by simp
  qed
  have j: "dbin_join (mk_djoin acc c) (dtabc n acc T) False (dtabc n c V)
      = dtabc n acc (join T False V)" using j0 by (simp add: mc)
  have t: "table n (set acc) (join T False V)"
    using Cons(4) wf sub by (auto intro: join_table[of n "set acc" T "set c" V False])
  have "dands_neg (dands_plans acc (c # cs)) (dtabc n acc T) (map2 (dtabc n) (c # cs) Vs)
      = dands_neg (dands_plans acc cs) (dtabc n acc (join T False V)) (map2 (dtabc n) cs Vs')"
    unfolding V by (simp add: j mc)
  also have "\<dots> = dtabc n acc (kands_neg (join T False V) Vs')"
  proof (rule Cons(1))
    show "sorted_wrt (<) acc" by (rule Cons(2))
    show "\<forall>d \<in> set acc. d < n" by (rule Cons(3))
    show "table n (set acc) (join T False V)" by (rule t)
    show "finite (join T False V)" using Cons(5) wf by (simp add: finite_join)
    show "list_all2 (wf_operand n) cs Vs'" by (rule rest)
    show "\<forall>d \<in> set cs. set d \<subseteq> set acc" using Cons(7) by simp
  qed
  finally show ?case unfolding V by simp
qed simp

subsubsection \<open>The kernel's multi-way join is the same left-to-right fold\<close>

lemma mmulti_join'_single:
  assumes "table n A X" "wf_set n A"
  shows "mmulti_join' [A] [] [X] = X"
proof (intro set_eqI iffI)
  fix z assume "z \<in> mmulti_join' [A] [] [X]"
  then have "wf_tuple n A z" "restrict A z \<in> X"
    using mmulti_join'_correct[of "[A]" n "[]" "[X]" z] assms by auto
  then show "z \<in> X" by (simp add: restrict_idle)
next
  fix z assume z: "z \<in> X"
  then have w: "wf_tuple n A z" using assms by (simp add: table_def)
  then show "z \<in> mmulti_join' [A] [] [X]"
    using mmulti_join'_correct[of "[A]" n "[]" "[X]" z] assms z by (simp add: restrict_idle)
qed

lemma mmulti_join'_peel_pos:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) ((A0 # A1 # As) @ A_neg) ((X0 # X1 # Xs) @ L_neg)"
    and "length As = length Xs"
  shows "mmulti_join' (A0 # A1 # As) A_neg ((X0 # X1 # Xs) @ L_neg)
       = mmulti_join' ((A0 \<union> A1) # As) A_neg ((join X0 True X1 # Xs) @ L_neg)"
  using mmulti_join'_opt_True[of n "[]" A0 "[]" A1 As A_neg "[]" X0 "[]" X1 Xs L_neg] assms
  by simp

lemma mmulti_join'_peel_neg:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) ([A0] @ (B0 # Bs)) ([X0] @ (Y0 # Ys))"
    and "length Bs = length Ys" and "B0 \<subseteq> A0"
  shows "mmulti_join' [A0] (B0 # Bs) (X0 # Y0 # Ys)
       = mmulti_join' [A0] Bs (join X0 False Y0 # Ys)"
  using mmulti_join'_opt_False[where n = n and A_zs = "[]" and A_x = A0 and A_xs = "[]"
      and A_ws = "[]" and A_y = B0 and A_ys = Bs
      and zs = "[]" and x = X0 and xs = "[]" and ws = "[]" and y = Y0 and ys = Ys] assms
  by (simp del: mmulti_join'.simps)

lemma wf_set_finite: "wf_set n A \<Longrightarrow> finite A"
  unfolding wf_set_def by (rule bounded_nat_set_is_finite)

lemma mmulti_join'_fold_pos:
  "\<And>A0 X0 A_neg L_neg. length As = length Xs \<Longrightarrow>
   list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) ((A0 # As) @ A_neg) ((X0 # Xs) @ L_neg) \<Longrightarrow>
   mmulti_join' (A0 # As) A_neg ((X0 # Xs) @ L_neg)
     = mmulti_join' [A0 \<union> \<Union>(set As)] A_neg (kands_pos X0 Xs # L_neg)"
proof (induct As Xs rule: list_induct2')
  case (4 A1 As X1 Xs)
  have "mmulti_join' (A0 # A1 # As) A_neg ((X0 # X1 # Xs) @ L_neg)
      = mmulti_join' ((A0 \<union> A1) # As) A_neg ((join X0 True X1 # Xs) @ L_neg)"
    using 4(2,3) by (intro mmulti_join'_peel_pos) auto
  also have "\<dots> = mmulti_join' [(A0 \<union> A1) \<union> \<Union>(set As)] A_neg (kands_pos (join X0 True X1) Xs # L_neg)"
    using 4(2,3) by (intro 4(1)) (auto simp: list_all2_Cons1 list_all2_append1 wf_set_def
        intro!: join_table[of n A0 X0 A1 X1 True])
  finally show ?case by (simp add: Un_assoc)
qed auto

lemma mmulti_join'_fold_neg:
  "\<And>A0 X0. length Bs = length Ys \<Longrightarrow>
   list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) ([A0] @ Bs) ([X0] @ Ys) \<Longrightarrow>
   \<forall>B \<in> set Bs. B \<subseteq> A0 \<Longrightarrow>
   mmulti_join' [A0] Bs (X0 # Ys) = kands_neg X0 Ys"
proof (induct Bs Ys rule: list_induct2')
  case (1 A0 X0)
  then show ?case by (auto simp add: mmulti_join'_single simp del: mmulti_join'.simps)
next
  case (4 B0 Bs Y0 Ys A0 X0)
  have tabs: "table n A0 X0" "wf_set n A0" "table n B0 Y0" "wf_set n B0"
    using 4(3) by (auto simp: list_all2_Cons1)
  have sub: "B0 \<subseteq> A0" using 4(4) by simp
  have "mmulti_join' [A0] (B0 # Bs) (X0 # Y0 # Ys)
      = mmulti_join' [A0] Bs (join X0 False Y0 # Ys)"
    using 4(2,3) sub by (intro mmulti_join'_peel_neg) auto
  also have "\<dots> = kands_neg (join X0 False Y0) Ys"
  proof (rule 4(1))
    show "length Bs = length Ys" using 4(2) by simp
    show "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) ([A0] @ Bs) ([join X0 False Y0] @ Ys)"
      using 4(3) tabs sub by (auto simp: list_all2_Cons1
          intro!: join_table[of n A0 X0 B0 Y0 False])
    show "\<forall>B \<in> set Bs. B \<subseteq> A0" using 4(4) by simp
  qed
  finally show ?case by simp
qed (auto simp del: mmulti_join'.simps)

subsubsection \<open>The two agree\<close>

lemma list_all2_wf_of_operand:
  "list_all2 (wf_operand n) cs Us \<Longrightarrow> list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (map set cs) Us"
  by (induct rule: list_all2_induct) (auto simp: wf_set_def)

lemma kands_pos_table:
  "list_all2 (wf_operand n) css Us \<Longrightarrow> table n A T \<Longrightarrow>
     table n (A \<union> (\<Union>c \<in> set css. set c)) (kands_pos T Us)"
proof (induct css Us arbitrary: A T rule: list_all2_induct)
  case (Cons c cs U Us)
  have "table n (A \<union> set c) (join T True U)"
    using Cons(1,4) by (auto intro!: join_table[of n A T "set c" U True])
  from Cons(3)[OF this] show ?case by (simp add: Un_assoc)
qed simp

lemma wf_operand_bounds:
  "list_all2 (wf_operand n) css Us \<Longrightarrow> \<forall>c \<in> set css. \<forall>d \<in> set c. d < n"
  by (induct rule: list_all2_induct) auto

lemma wf_operand_sorted:
  "list_all2 (wf_operand n) css Us \<Longrightarrow> \<forall>c \<in> set css. sorted_wrt (<) c"
  by (induct rule: list_all2_induct) auto

lemma kands_pos_finite: "list_all2 (wf_operand n) css Us \<Longrightarrow> finite T \<Longrightarrow> finite (kands_pos T Us)"
  by (induct css Us arbitrary: T rule: list_all2_induct) (auto simp: finite_join)

text \<open>The whole multi-way join: the dense left-to-right fold against the plan list is the short
  form of the kernel's @{const mmulti_join'}.\<close>

theorem dmulti_join_dtabc:
  assumes s0: "sorted_wrt (<) c0" and b0: "\<forall>d \<in> set c0. d < n"
    and t0: "table n (set c0) T0" and f0: "finite T0"
    and pos: "list_all2 (wf_operand n) css Us"
    and neg: "list_all2 (wf_operand n) nss Vs"
    and sub: "\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css)"
  shows "dands_neg (dands_plans (dands_cols c0 css) nss)
           (dands_pos (dands_plans c0 css) (dtabc n c0 T0) (map2 (dtabc n) css Us))
           (map2 (dtabc n) nss Vs)
       = dtabc n (dands_cols c0 css)
           (mmulti_join' (set c0 # map set css) (map set nss) ((T0 # Us) @ Vs))"
proof -
  let ?A = "set (dands_cols c0 css)"
  have lp: "length (map set css) = length Us" using pos by (simp add: list_all2_lengthD)
  have ln: "length (map set nss) = length Vs" using neg by (simp add: list_all2_lengthD)
  have la: "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
      ((set c0 # map set css) @ map set nss) ((T0 # Us) @ Vs)"
    using t0 b0 list_all2_wf_of_operand[OF pos] list_all2_wf_of_operand[OF neg]
    by (simp add: wf_set_def list_all2_appendI)
  have A_eq: "set c0 \<union> (\<Union>c \<in> set css. set c) = ?A" by (simp add: set_dands_cols)
  have tk: "table n ?A (kands_pos T0 Us)"
    using kands_pos_table[OF pos t0] by (simp add: set_dands_cols)
  have fk: "finite (kands_pos T0 Us)" by (rule kands_pos_finite[OF pos f0])
  have "mmulti_join' (set c0 # map set css) (map set nss) ((T0 # Us) @ Vs)
      = mmulti_join' [?A] (map set nss) (kands_pos T0 Us # Vs)"
    using mmulti_join'_fold_pos[OF lp la] by (simp add: A_eq del: mmulti_join'.simps)
  also have "\<dots> = kands_neg (kands_pos T0 Us) Vs"
  proof (rule mmulti_join'_fold_neg)
    show "length (map set nss) = length Vs" by (rule ln)
    show "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
        ([?A] @ map set nss) ([kands_pos T0 Us] @ Vs)"
      using tk b0 wf_operand_bounds[OF pos] list_all2_wf_of_operand[OF neg]
      by (auto simp: wf_set_def set_dands_cols intro!: list_all2_appendI)
    show "\<forall>B \<in> set (map set nss). B \<subseteq> ?A" using sub by auto
  qed
  finally have kernel: "mmulti_join' (set c0 # map set css) (map set nss) ((T0 # Us) @ Vs)
      = kands_neg (kands_pos T0 Us) Vs" .
  have sacc: "sorted_wrt (<) (dands_cols c0 css)"
    by (rule sorted_dands_cols[OF s0 wf_operand_sorted[OF pos]])
  have bacc: "\<forall>d \<in> ?A. d < n"
    using b0 wf_operand_bounds[OF pos] by (auto simp: set_dands_cols)
  have "dands_pos (dands_plans c0 css) (dtabc n c0 T0) (map2 (dtabc n) css Us)
      = dtabc n (dands_cols c0 css) (kands_pos T0 Us)"
    by (rule dands_pos_dtabc[OF s0 b0 t0 f0 pos])
  then have "dands_neg (dands_plans (dands_cols c0 css) nss)
        (dands_pos (dands_plans c0 css) (dtabc n c0 T0) (map2 (dtabc n) css Us))
        (map2 (dtabc n) nss Vs)
      = dtabc n (dands_cols c0 css) (kands_neg (kands_pos T0 Us) Vs)"
    using dands_neg_dtabc[OF sacc bacc tk fk neg] sub by simp
  then show ?thesis using kernel by simp
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

text \<open>The re-indexed term read at the short tuple's positions is the original term read at the
  wide one's.\<close>

lemma meval_trm_reindex:
  "Formula.fv_trm t \<subseteq> set cs \<Longrightarrow>
     meval_trm (reindex_trm cs t) (map (\<lambda>c. x ! c) cs) = meval_trm t x"
  by (induct t) (auto simp: col_pos_nth)

subsection \<open>The group key is a suffix in both representations\<close>

text \<open>
  The aggregation's bound variables occupy the bottom of the frame and are contained in the
  operand's free variables, so the operand's column list is @{term "[0..<m]"} followed by the
  group's columns shifted up by @{term m}.  Under that decomposition the group key -- which the
  kernel takes as @{term "drop m"} of the wide tuple -- is @{term "drop m"} of the short one.
\<close>

abbreviation agg_cols :: "nat \<Rightarrow> cols \<Rightarrow> cols" where
  "agg_cols m gcols \<equiv> [0..<m] @ map (\<lambda>c. c + m) gcols"

lemma agg_cols_sorted:
  "sorted_wrt (<) gcols \<Longrightarrow> sorted_wrt (<) (agg_cols m gcols)"
  by (auto simp: sorted_wrt_append sorted_wrt_map)

lemma agg_cols_bound:
  "\<forall>c \<in> set gcols. c < n \<Longrightarrow> \<forall>c \<in> set (agg_cols m gcols). c < m + n"
  by auto

lemma drop_dproj_agg:
  assumes sg: "sorted_wrt (<) gcols" and bg: "\<forall>c \<in> set gcols. c < n"
    and lx: "length x = m + n"
  shows "drop m (dproj (wide_mask (m + n) (agg_cols m gcols)) x)
       = dproj (wide_mask n gcols) (drop m x)"
proof -
  have ld: "length (drop m x) = n" using lx by simp
  have "dproj (wide_mask (m + n) (agg_cols m gcols)) x = map (\<lambda>c. x ! c) (agg_cols m gcols)"
    by (rule dproj_wide_mask_eq_map_nth[OF agg_cols_sorted[OF sg] agg_cols_bound[OF bg] lx])
  then have "drop m (dproj (wide_mask (m + n) (agg_cols m gcols)) x)
      = map (\<lambda>c. x ! (c + m)) gcols" by simp
  moreover have "dproj (wide_mask n gcols) (drop m x) = map (\<lambda>c. x ! (c + m)) gcols"
    using dproj_wide_mask_eq_map_nth[OF sg bg ld] bg lx
    by (auto simp: add.commute cong: map_cong)
  ultimately show ?thesis by simp
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

text \<open>The kernel writes the aggregate at position @{term y} of the group key; over short tuples
  it goes at the one position @{term y} occupies among the group's columns.\<close>

lemma dproj_list_update:
  assumes s: "sorted_wrt (<) gcols" and b: "\<forall>c \<in> set gcols. c < n"
    and yn: "y < n" and yg: "y \<notin> set gcols" and lk: "length k = n"
  shows "dproj (wide_mask n (merge_cols gcols [y])) (k[y := Some v])
       = take (ins_pos gcols y) (dproj (wide_mask n gcols) k) @ Some v
         # drop (ins_pos gcols y) (dproj (wide_mask n gcols) k)"
proof -
  let ?p = "ins_pos gcols y"
  have sm: "sorted_wrt (<) (merge_cols gcols [y])" using s by (simp add: sorted_merge_cols)
  have bm: "\<forall>c \<in> set (merge_cols gcols [y]). c < n" using b yn by (simp add: set_merge_cols)
  have lu: "length (k[y := Some v]) = n" using lk by simp
  have "dproj (wide_mask n (merge_cols gcols [y])) (k[y := Some v])
      = map (\<lambda>c. (k[y := Some v]) ! c) (merge_cols gcols [y])"
    by (rule dproj_wide_mask_eq_map_nth[OF sm bm lu])
  also have "\<dots> = map (\<lambda>c. (k[y := Some v]) ! c) (take ?p gcols @ y # drop ?p gcols)"
    by (simp add: merge_cols_single[OF s yg])
  also have "\<dots> = map (\<lambda>c. k ! c) (take ?p gcols) @ Some v # map (\<lambda>c. k ! c) (drop ?p gcols)"
  proof -
    have upd: "\<And>c. c \<in> set gcols \<Longrightarrow> (k[y := Some v]) ! c = k ! c"
    proof -
      fix c assume "c \<in> set gcols"
      then have "y \<noteq> c" using yg by auto
      then show "(k[y := Some v]) ! c = k ! c" by simp
    qed
    have t: "map (\<lambda>c. (k[y := Some v]) ! c) (take ?p gcols) = map (\<lambda>c. k ! c) (take ?p gcols)"
      by (rule map_cong[OF refl]) (auto dest: in_set_takeD intro!: upd)
    have d: "map (\<lambda>c. (k[y := Some v]) ! c) (drop ?p gcols) = map (\<lambda>c. k ! c) (drop ?p gcols)"
      by (rule map_cong[OF refl]) (auto dest: in_set_dropD intro!: upd)
    show ?thesis using t d yn lk by simp
  qed
  also have "\<dots> = take ?p (map (\<lambda>c. k ! c) gcols) @ Some v # drop ?p (map (\<lambda>c. k ! c) gcols)"
    by (simp add: take_map drop_map)
  finally show ?thesis using dproj_wide_mask_eq_map_nth[OF s b lk] by simp
qed

subsection \<open>The group is a table over the group's columns\<close>

lemma wf_tuple_drop_agg:
  "wf_tuple (m + n) (set (agg_cols m gcols)) x \<Longrightarrow> wf_tuple n (set gcols) (drop m x)"
  by (auto simp: wf_tuple_def)

lemma ecard_image: "inj_on f A \<Longrightarrow> ecard (f ` A) = ecard A"
  by (simp add: ecard_def card_image finite_image_iff)

lemma inj_on_dproj_cols:
  "sorted_wrt (<) cs \<Longrightarrow> inj_on (dproj (wide_mask n cs)) {x. wf_tuple n (set cs) x}"
  by (simp add: wide_mask_eq_join_mask inj_on_dproj_wf)

lemma dproj_cols_eq_iff:
  assumes s: "sorted_wrt (<) cs"
    and x: "wf_tuple n (set cs) x" and y: "wf_tuple n (set cs) y"
  shows "(dproj (wide_mask n cs) x = dproj (wide_mask n cs) y) = (x = y)"
  using inj_on_dproj_cols[OF s, of n] x y by (auto simp: inj_on_def)

lemma drop_dtabc_agg:
  assumes sg: "sorted_wrt (<) gcols" and bg: "\<forall>c \<in> set gcols. c < n"
    and rel: "table (m + n) (set (agg_cols m gcols)) rel"
  shows "drop m ` dtabc (m + n) (agg_cols m gcols) rel = dtabc n gcols (drop m ` rel)"
proof -
  have "\<And>x. x \<in> rel \<Longrightarrow> length x = m + n" using rel by (auto simp: table_def wf_tuple_def)
  then show ?thesis
    unfolding dtabc_def image_image
    by (intro image_cong refl) (simp add: drop_dproj_agg[OF sg bg])
qed

text \<open>Selecting a group commutes with narrowing: the short tuples whose key is the short form of
  @{term "drop m x0"} are exactly the short forms of the wide tuples whose key is @{term "drop m x0"}.\<close>

lemma dtabc_agg_group:
  assumes sg: "sorted_wrt (<) gcols" and bg: "\<forall>c \<in> set gcols. c < n"
    and rel: "table (m + n) (set (agg_cols m gcols)) rel" and x0: "x0 \<in> rel"
  shows "Set.filter (\<lambda>z. drop m z = dproj (wide_mask n gcols) (drop m x0))
           (dtabc (m + n) (agg_cols m gcols) rel)
       = dtabc (m + n) (agg_cols m gcols) (Set.filter (\<lambda>x. drop m x = drop m x0) rel)"
proof -
  have wf: "\<And>x. x \<in> rel \<Longrightarrow> wf_tuple (m + n) (set (agg_cols m gcols)) x"
    using rel by (simp add: table_def)
  then have len: "\<And>x. x \<in> rel \<Longrightarrow> length x = m + n" by (simp add: wf_tuple_def)
  have key: "\<And>x. x \<in> rel \<Longrightarrow>
      (drop m (dproj (wide_mask (m + n) (agg_cols m gcols)) x)
         = dproj (wide_mask n gcols) (drop m x0)) = (drop m x = drop m x0)"
    by (simp add: drop_dproj_agg[OF sg bg len]
        dproj_cols_eq_iff[OF sg wf_tuple_drop_agg[OF wf] wf_tuple_drop_agg[OF wf[OF x0]]])
  show ?thesis unfolding dtabc_def by (auto simp: key)
qed

subsection \<open>The aggregated values do not change\<close>

lemma agg_values_dtabc:
  assumes sg: "sorted_wrt (<) gcols" and bg: "\<forall>c \<in> set gcols. c < n"
    and tG: "table (m + n) (set (agg_cols m gcols)) G"
    and fv: "Formula.fv_trm f \<subseteq> set (agg_cols m gcols)"
  shows "agg_values (reindex_trm (agg_cols m gcols) f) (dtabc (m + n) (agg_cols m gcols) G)
       = agg_values f G"
proof -
  let ?cc = "agg_cols m gcols"
  let ?M = "wide_mask (m + n) ?cc"
  let ?g = "reindex_trm ?cc f"
  have wf: "\<And>x. x \<in> G \<Longrightarrow> wf_tuple (m + n) (set ?cc) x" using tG by (simp add: table_def)
  then have len: "\<And>x. x \<in> G \<Longrightarrow> length x = m + n" by (simp add: wf_tuple_def)
  have ev: "\<And>x. x \<in> G \<Longrightarrow> meval_trm ?g (dproj ?M x) = meval_trm f x"
  proof -
    fix x assume x: "x \<in> G"
    have "meval_trm ?g (map (\<lambda>c. x ! c) ?cc) = meval_trm f x"
      by (rule meval_trm_reindex[OF fv])
    then show "meval_trm ?g (dproj ?M x) = meval_trm f x"
      by (simp only: dproj_wide_mask_eq_map_nth[OF agg_cols_sorted[OF sg]
            agg_cols_bound[OF bg] len[OF x]])
  qed
  have inj: "inj_on (dproj ?M) G"
    by (rule inj_on_subset[OF inj_on_dproj_cols[OF agg_cols_sorted[OF sg]]]) (blast intro: wf)
  have img: "meval_trm ?g ` dproj ?M ` G = meval_trm f ` G"
    unfolding image_image by (intro image_cong[OF refl] ev)
  have "agg_values ?g (dproj ?M ` G)
      = (\<lambda>v. (v, ecard (Set.filter (\<lambda>x. meval_trm f x = v) G))) ` meval_trm f ` G"
    unfolding agg_values img
  proof (intro image_cong[OF refl])
    fix v :: event_data
    have fil: "Set.filter (\<lambda>z. meval_trm ?g z = v) (dproj ?M ` G)
        = dproj ?M ` Set.filter (\<lambda>x. meval_trm f x = v) G"
      by (auto simp: ev)
    have inj': "inj_on (dproj ?M) (Set.filter (\<lambda>x. meval_trm f x = v) G)"
      by (rule inj_on_subset[OF inj]) auto
    show "(v, ecard (Set.filter (\<lambda>z. meval_trm ?g z = v) (dproj ?M ` G)))
        = (v, ecard (Set.filter (\<lambda>x. meval_trm f x = v) G))"
      unfolding fil ecard_image[OF inj'] by (rule refl)
  qed
  also have "\<dots> = agg_values f G" by (simp add: agg_values)
  finally show ?thesis unfolding dtabc_def .
qed

subsection \<open>Aggregation over short tuples agrees with the kernel's\<close>

text \<open>
  The dense aggregation takes the group key as a suffix of the short tuple (of length
  @{term "length tys"} before it, exactly as in the wide frame), and writes the aggregate at the
  position @{term y} occupies among the group's columns rather than at @{term y} itself.
\<close>

definition dagg :: "bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> Formula.trm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    event_data table \<Rightarrow> event_data table" where
  "dagg g0 \<omega> f k pos rel =
     (if g0 \<and> Set.is_empty rel then {[Some (eval_agg_op \<omega> {})]}
      else (let groups = cluster (Some \<circ> drop k) rel in
        (\<lambda>g. case Mapping.lookup groups g of
                None \<Rightarrow> g
              | Some G \<Rightarrow> take pos g @ Some (eval_agg_op \<omega> (agg_values f G)) # drop pos g)
          ` Mapping.keys groups))"

theorem dagg_eval_agg:
  assumes sg: "sorted_wrt (<) gcols" and bg: "\<forall>c \<in> set gcols. c < n"
    and yn: "y < n" and yg: "y \<notin> set gcols"
    and rel: "table (length tys + n) (set (agg_cols (length tys) gcols)) rel"
    and fv: "Formula.fv_trm f \<subseteq> set (agg_cols (length tys) gcols)"
    and g0: "g0 \<Longrightarrow> gcols = []"
  shows "dagg g0 \<omega> (reindex_trm (agg_cols (length tys) gcols) f) (length tys) (ins_pos gcols y)
           (dtabc (length tys + n) (agg_cols (length tys) gcols) rel)
       = dtabc n (merge_cols gcols [y]) (eval_agg n g0 y \<omega> tys f rel)"
proof -
  let ?m = "length tys"
  let ?cc = "agg_cols ?m gcols"
  let ?M = "wide_mask (?m + n) ?cc"
  let ?G = "wide_mask n gcols"
  let ?R = "wide_mask n (merge_cols gcols [y])"
  let ?g = "reindex_trm ?cc f"
  let ?p = "ins_pos gcols y"
  let ?z = "eval_agg_op \<omega> {}"
  let ?A = "\<lambda>x. eval_agg_op \<omega>
     (agg_values f (Set.filter (\<lambda>x'. drop ?m x' = drop ?m x) rel))"
  have wf: "\<And>x. x \<in> rel \<Longrightarrow> wf_tuple (?m + n) (set ?cc) x" using rel by (simp add: table_def)
  then have len: "\<And>x. x \<in> rel \<Longrightarrow> length x = ?m + n" by (simp add: wf_tuple_def)
  show ?thesis
  proof (cases "g0 \<and> rel = empty_table")
    case True
    then have e: "rel = {}" and g: "g0" by (auto simp: empty_table_def)
    have mc: "merge_cols gcols [y] = [y]" using g0[OF g] by simp
    let ?t = "Table.tabulate (\<lambda>j. if y = j then Some ?z else None) 0 n"
    have "dtabc n (merge_cols gcols [y]) (eval_agg n g0 y \<omega> tys f rel)
        = {dproj (wide_mask n [y]) ?t}"
      using True by (simp add: eval_agg_def dtabc_def singleton_table_def mc)
    also have "\<dots> = {[Some ?z]}"
      using yn by (simp add: dproj_wide_mask_eq_map_nth[where cs="[y]"])
    finally show ?thesis using e g by (simp add: dagg_def dtabc_def)
  next
    case False
    then have ne: "\<not> (g0 \<and> rel = empty_table)" by simp
    then have ne': "\<not> (g0 \<and> Set.is_empty (dproj ?M ` rel))"
      by (auto simp: empty_table_def)
    have "dagg g0 \<omega> ?g ?m ?p (dtabc (?m + n) ?cc rel)
        = (\<lambda>k. case Mapping.lookup (cluster (Some \<circ> drop ?m) (dproj ?M ` rel)) k of
                 None \<Rightarrow> k
               | Some G \<Rightarrow> take ?p k @ Some (eval_agg_op \<omega> (agg_values ?g G)) # drop ?p k)
          ` (drop ?m ` dproj ?M ` rel)"
      unfolding dagg_def dtabc_def Let_def keys_cluster using ne' by simp
    also have "\<dots> = (\<lambda>k. take ?p k @ Some (eval_agg_op \<omega>
          (agg_values ?g (Set.filter (\<lambda>z. drop ?m z = k) (dproj ?M ` rel)))) # drop ?p k)
          ` (drop ?m ` dproj ?M ` rel)"
      by (intro image_cong[OF refl]) (simp add: lookup_cluster_Some)
    also have "\<dots> = (\<lambda>x. dproj ?R ((drop ?m x)[y := Some (?A x)])) ` rel"
      unfolding image_image
    proof (intro image_cong[OF refl])
      fix x assume x: "x \<in> rel"
      let ?gr = "Set.filter (\<lambda>x'. drop ?m x' = drop ?m x) rel"
      have k: "drop ?m (dproj ?M x) = dproj ?G (drop ?m x)"
        by (rule drop_dproj_agg[OF sg bg len[OF x]])
      have grp: "Set.filter (\<lambda>z. drop ?m z = dproj ?G (drop ?m x)) (dproj ?M ` rel)
          = dproj ?M ` ?gr"
        using dtabc_agg_group[OF sg bg rel x] unfolding dtabc_def .
      have tgr: "table (?m + n) (set ?cc) ?gr" using rel by (auto simp: table_def)
      have av: "agg_values ?g (dproj ?M ` ?gr) = agg_values f ?gr"
        using agg_values_dtabc[OF sg bg tgr fv] unfolding dtabc_def .
      have upd: "dproj ?R ((drop ?m x)[y := Some (?A x)])
          = take ?p (dproj ?G (drop ?m x)) @ Some (?A x) # drop ?p (dproj ?G (drop ?m x))"
        by (rule dproj_list_update[OF sg bg yn yg]) (simp add: len[OF x])
      show "take ?p (drop ?m (dproj ?M x)) @ Some (eval_agg_op \<omega>
              (agg_values ?g (Set.filter (\<lambda>z. drop ?m z = drop ?m (dproj ?M x))
                 (dproj ?M ` rel)))) # drop ?p (drop ?m (dproj ?M x))
          = dproj ?R ((drop ?m x)[y := Some (?A x)])"
        unfolding upd k grp av by (rule refl)
    qed
    also have "\<dots> = dtabc n (merge_cols gcols [y]) (eval_agg n g0 y \<omega> tys f rel)"
      unfolding dtabc_def eval_agg_def Let_def agg_values by (simp add: ne image_image)
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

subsection \<open>Narrowing at the boundary with the unmodified evaluator\<close>

definition all_true :: "bool list \<Rightarrow> bool" where
  "all_true bs = list_all id bs"

lemma dproj_all_true: "all_true bs \<Longrightarrow> length xs = length bs \<Longrightarrow> dproj bs xs = xs"
  by (induct bs xs rule: dproj.induct) (auto simp: all_true_def)

definition dnarrow :: "bool list \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "dnarrow msk r = (if all_true msk then r else dproj msk ` r)"

text \<open>When every column is present the mask is the identity, so the narrowing of a table that
  already has no holes costs nothing.\<close>

lemma dnarrow_dtabc:
  assumes "table n (set cs) T"
  shows "dnarrow (wide_mask n cs) T = dtabc n cs T"
proof (cases "all_true (wide_mask n cs)")
  case True
  have "\<And>x. x \<in> T \<Longrightarrow> dproj (wide_mask n cs) x = x"
    using assms True by (auto simp: table_def wf_tuple_def intro!: dproj_all_true)
  then show ?thesis using True by (auto simp: dnarrow_def dtabc_def intro!: rev_image_eqI)
qed (simp add: dnarrow_def dtabc_def)

subsection \<open>Matching a predicate's arguments\<close>

definition dmatch_table :: "Formula.trm list \<Rightarrow> cols \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dmatch_table tms cs X = Option.these ((\<lambda>x. map_option (\<lambda>f. map f cs) (match tms x)) ` X)"

lemma these_map_option_image: "Option.these (map_option g ` S) = g ` Option.these S"
  by (force simp: Option.these_def image_iff)

text \<open>The kernel writes the matching assignment into a tuple of the full width; over short
  tuples it is read off at the predicate's columns.\<close>

theorem dmatch_table_dtabc:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
  shows "dmatch_table tms cs X
       = dtabc n cs ((\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` X))"
proof -
  have t: "\<And>f :: nat \<Rightarrow> event_data option.
      dproj (wide_mask n cs) (Table.tabulate f 0 n) = map f cs"
  proof -
    fix f :: "nat \<Rightarrow> event_data option"
    have "dproj (wide_mask n cs) (Table.tabulate f 0 n)
        = map (\<lambda>c. Table.tabulate f 0 n ! c) cs"
      by (rule dproj_wide_mask_eq_map_nth[OF s b]) simp
    also have "\<dots> = map f cs" using b by (auto intro!: map_cong[OF refl])
    finally show "dproj (wide_mask n cs) (Table.tabulate f 0 n) = map f cs" .
  qed
  have "dmatch_table tms cs X = (\<lambda>f. map f cs) ` Option.these (match tms ` X)"
    unfolding dmatch_table_def image_image[symmetric] these_map_option_image
    by (rule refl)
  also have "\<dots> = dtabc n cs ((\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` X))"
    unfolding dtabc_def image_image by (simp add: t)
  finally show ?thesis .
qed

subsection \<open>A predicate whose arguments are distinct variables in ascending order\<close>

text \<open>Then the argument tuples of the database are already the short tuples: the kernel's
  @{const simple_match} spreads them over the full width, and narrowing puts them back.\<close>

fun smp_cols :: "Formula.trm list \<Rightarrow> cols" where
  "smp_cols [] = []"
| "smp_cols (Formula.Var y # ts) = y # smp_cols ts"
| "smp_cols (t # ts) = []"

lemma smp_cols_sorted:
  "is_simple_pattern tms m \<Longrightarrow> sorted_wrt (<) (smp_cols tms) \<and> (\<forall>y \<in> set (smp_cols tms). m \<le> y)"
  by (induct tms m rule: is_simple_pattern.induct) force+

lemma dproj_simple_match:
  "is_simple_pattern tms m \<Longrightarrow> length x = length tms \<Longrightarrow>
   \<forall>y \<in> set (smp_cols tms). y < n \<Longrightarrow> m \<le> n \<Longrightarrow>
   dproj (wide_mask_at m (n - m) (smp_cols tms)) (simple_match n m tms x) = x"
proof (induct n m tms x rule: simple_match.induct)
  case (1 n m)
  then show ?case by (simp add: wide_mask_at_Nil dproj_replicate_False)
next
  case (2 n m y ts v vs)
  have my: "m \<le> y" and sp: "is_simple_pattern ts (Suc y)" using 2(3) by simp_all
  have yn: "y < n" using 2(5) by simp
  then have mn: "m < n" using my by simp
  have k: "n - m = Suc (n - Suc m)" using mn by simp
  show ?case
  proof (cases "m < y")
    case True
    have "dproj (wide_mask_at (Suc m) (n - Suc m) (smp_cols (Formula.Var y # ts)))
        (simple_match n (Suc m) (Formula.Var y # ts) (v # vs)) = v # vs"
    proof (rule 2(1))
      show "m < y" by (rule True)
      show "is_simple_pattern (Formula.Var y # ts) (Suc m)" using True sp by simp
      show "length (v # vs) = length (Formula.Var y # ts)" using 2(4) by simp
      show "\<forall>z \<in> set (smp_cols (Formula.Var y # ts)). z < n" using 2(5) by simp
      show "Suc m \<le> n" using mn by simp
    qed
    then show ?thesis using True by (simp add: k)
  next
    case False
    then have ym: "y = m" using my by simp
    have "dproj (wide_mask_at (Suc m) (n - Suc m) (smp_cols ts)) (simple_match n (Suc m) ts vs) = vs"
    proof (rule 2(2))
      show "\<not> m < y" by (rule False)
      show "is_simple_pattern ts (Suc m)" using sp ym by simp
      show "length vs = length ts" using 2(4) by simp
      show "\<forall>z \<in> set (smp_cols ts). z < n" using 2(5) by simp
      show "Suc m \<le> n" using mn by simp
    qed
    then show ?thesis using False ym by (simp add: k)
  qed
qed auto

lemma dproj_simple_match0:
  "is_simple_pattern tms 0 \<Longrightarrow> length x = length tms \<Longrightarrow> \<forall>y \<in> set (smp_cols tms). y < n \<Longrightarrow>
     dproj (wide_mask n (smp_cols tms)) (simple_match n 0 tms x) = x"
  using dproj_simple_match[of tms 0 x n] by (simp add: wide_mask_def)

theorem dtabc_simple_match:
  assumes sp: "is_simple_pattern tms 0" and b: "\<forall>y \<in> set (smp_cols tms). y < n"
    and l: "\<forall>x \<in> X. length x = length tms"
  shows "dtabc n (smp_cols tms) (simple_match n 0 tms ` X) = X"
proof -
  have e: "\<And>x. x \<in> X \<Longrightarrow> dproj (wide_mask n (smp_cols tms)) (simple_match n 0 tms x) = x"
    using l b by (intro dproj_simple_match0[OF sp]) auto
  have "(\<lambda>x. dproj (wide_mask n (smp_cols tms)) (simple_match n 0 tms x)) ` X = (\<lambda>x. x) ` X"
    by (rule image_cong[OF refl]) (rule e)
  then show ?thesis unfolding dtabc_def image_image by simp
qed

subsection \<open>The existential\<close>

text \<open>
  The kernel drops the first component of every tuple.  Over short tuples the first column is
  either present -- and then it is the head, which is dropped -- or absent, and then there is
  nothing to do; either way the remaining columns move down by one.
\<close>

definition ex_drop0 :: "cols \<Rightarrow> bool" where
  "ex_drop0 ccs = (case ccs of [] \<Rightarrow> False | c # _ \<Rightarrow> c = 0)"

definition ex_cols :: "cols \<Rightarrow> cols" where
  "ex_cols ccs = map (\<lambda>c. c - Suc 0) (if ex_drop0 ccs then tl ccs else ccs)"

lemma ex_cols_pos: "sorted_wrt (<) ccs \<Longrightarrow> \<forall>c \<in> set (if ex_drop0 ccs then tl ccs else ccs). 0 < c"
  by (cases ccs) (auto simp: ex_drop0_def)

lemma ex_cols_sorted:
  assumes "sorted_wrt (<) ccs" shows "sorted_wrt (<) (ex_cols ccs)"
proof -
  have s: "sorted_wrt (<) (if ex_drop0 ccs then tl ccs else ccs)"
    using assms by (cases ccs) (auto simp: ex_drop0_def)
  have p: "\<forall>c \<in> set (if ex_drop0 ccs then tl ccs else ccs). 0 < c"
    by (rule ex_cols_pos[OF assms])
  show ?thesis unfolding ex_cols_def sorted_wrt_map
    by (rule sorted_wrt_mono_rel[OF _ s]) (use p in auto)
qed

lemma nth_tl_Suc: "0 < c \<Longrightarrow> c < length x \<Longrightarrow> tl x ! (c - Suc 0) = x ! c"
  by (cases x) auto

lemma ex_cols_bound:
  "sorted_wrt (<) ccs \<Longrightarrow> \<forall>c \<in> set ccs. c < Suc n \<Longrightarrow> \<forall>c \<in> set (ex_cols ccs). c < n"
  using ex_cols_pos[of ccs] by (cases ccs) (auto simp: ex_cols_def ex_drop0_def)

lemma ex_cols_set:
  "sorted_wrt (<) ccs \<Longrightarrow> set (ex_cols ccs) = (\<lambda>c. c - Suc 0) ` (set ccs - {0})"
  by (cases ccs) (auto simp: ex_cols_def ex_drop0_def)

lemma table_tl:
  assumes s: "sorted_wrt (<) ccs" and t: "table (Suc n) (set ccs) T"
  shows "table n (set (ex_cols ccs)) (tl ` T)"
proof -
  have "\<And>x. x \<in> T \<Longrightarrow> wf_tuple n (set (ex_cols ccs)) (tl x)"
  proof -
    fix x assume "x \<in> T"
    then have w: "wf_tuple (Suc n) (set ccs) x" using t by (simp add: table_def)
    then have l: "length x = Suc n" by (simp add: wf_tuple_def)
    have "\<And>i. i < n \<Longrightarrow> (tl x ! i = None) = (i \<notin> set (ex_cols ccs))"
    proof -
      fix i assume i: "i < n"
      have "tl x ! i = x ! Suc i" using l i by (cases x) auto
      moreover have "(x ! Suc i = None) = (Suc i \<notin> set ccs)" using w i by (simp add: wf_tuple_def)
      moreover have "(Suc i \<in> set ccs) = (i \<in> set (ex_cols ccs))"
        using ex_cols_set[OF s] by force
      ultimately show "(tl x ! i = None) = (i \<notin> set (ex_cols ccs))" by simp
    qed
    then show "wf_tuple n (set (ex_cols ccs)) (tl x)" using l by (simp add: wf_tuple_def)
  qed
  then show ?thesis by (auto simp: table_def)
qed

theorem dtabc_exists:
  assumes s: "sorted_wrt (<) ccs" and b: "\<forall>c \<in> set ccs. c < Suc n"
    and t: "table (Suc n) (set ccs) T"
  shows "(if ex_drop0 ccs then tl ` dtabc (Suc n) ccs T else dtabc (Suc n) ccs T)
       = dtabc n (ex_cols ccs) (tl ` T)"
proof -
  let ?cs' = "if ex_drop0 ccs then tl ccs else ccs"
  have pos: "\<forall>c \<in> set ?cs'. 0 < c" by (rule ex_cols_pos[OF s])
  have s': "sorted_wrt (<) (ex_cols ccs)" by (rule ex_cols_sorted[OF s])
  have b': "\<forall>c \<in> set (ex_cols ccs). c < n" by (rule ex_cols_bound[OF s b])
  have "\<And>x. x \<in> T \<Longrightarrow>
      (if ex_drop0 ccs then tl (dproj (wide_mask (Suc n) ccs) x) else dproj (wide_mask (Suc n) ccs) x)
        = dproj (wide_mask n (ex_cols ccs)) (tl x)"
  proof -
    fix x assume "x \<in> T"
    then have w: "wf_tuple (Suc n) (set ccs) x" using t by (simp add: table_def)
    then have l: "length x = Suc n" by (simp add: wf_tuple_def)
    have lt: "length (tl x) = n" using l by simp
    have "dproj (wide_mask (Suc n) ccs) x = map (\<lambda>c. x ! c) ccs"
      by (rule dproj_wide_mask_eq_map_nth[OF s b l])
    then have lhs: "(if ex_drop0 ccs then tl (dproj (wide_mask (Suc n) ccs) x)
          else dproj (wide_mask (Suc n) ccs) x) = map (\<lambda>c. x ! c) ?cs'"
      by (cases ccs) (auto simp: ex_drop0_def)
    have "dproj (wide_mask n (ex_cols ccs)) (tl x) = map (\<lambda>c. tl x ! c) (ex_cols ccs)"
      by (rule dproj_wide_mask_eq_map_nth[OF s' b' lt])
    also have "\<dots> = map (\<lambda>c. tl x ! (c - Suc 0)) ?cs'" by (simp add: ex_cols_def)
    also have "\<dots> = map (\<lambda>c. x ! c) ?cs'"
    proof (rule map_cong[OF refl])
      fix c assume c: "c \<in> set ?cs'"
      then have c0: "0 < c" using pos by simp
      have "set ?cs' \<subseteq> set ccs" by (cases ccs) (auto simp: ex_drop0_def)
      then have "c < length x" using c b l by auto
      then show "tl x ! (c - Suc 0) = x ! c" by (rule nth_tl_Suc[OF c0])
    qed
    finally show "(if ex_drop0 ccs then tl (dproj (wide_mask (Suc n) ccs) x)
          else dproj (wide_mask (Suc n) ccs) x) = dproj (wide_mask n (ex_cols ccs)) (tl x)"
      using lhs by simp
  qed
  then show ?thesis unfolding dtabc_def image_image by (cases "ex_drop0 ccs") auto
qed

(*<*)
end
(*>*)
