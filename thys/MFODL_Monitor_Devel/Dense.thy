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

(*<*)
end
(*>*)
