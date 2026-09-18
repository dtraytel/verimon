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

fun dproj :: "bool list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
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

definition dtabc :: "nat \<Rightarrow> cols \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
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

definition dsemi :: "bool list \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
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

subsection \<open>The pair of morphisms\<close>

text \<open>
  Narrowing deletes the empty columns; widening puts them back.  The two are inverse bijections
  between the tables that are well formed over @{term "set cs"} in the wide frame and the tables
  of short tuples of length @{term "length cs"} with no holes at all.  Every theorem below is the
  statement that one operation commutes with this pair.
\<close>

definition dtabw :: "nat \<Rightarrow> cols \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "dtabw n cs D = dwiden (wide_mask n cs) ` D"

definition dwf_tuple :: "nat \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "dwf_tuple k d \<longleftrightarrow> length d = k \<and> (\<forall>i < k. d ! i \<noteq> None)"

definition dtable :: "cols \<Rightarrow> 'a table \<Rightarrow> bool" where
  "dtable cs D \<longleftrightarrow> (\<forall>d \<in> D. dwf_tuple (length cs) d)"

lemma nth_wide_mask:
  "sorted_wrt (<) cs \<Longrightarrow> i < n \<Longrightarrow> wide_mask n cs ! i = (i \<in> set cs)"
  unfolding wide_mask_def by (subst wide_mask_at_eq) auto

lemma length_filter_wide_mask:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
  shows "length (filter id (wide_mask n cs)) = length cs"
  using length_dproj[of "wide_mask n cs" "replicate n None"]
    dproj_wide_mask_eq_map_nth[OF s b, of "replicate n None"]
  by (metis length_map length_replicate length_wide_mask)

lemma dwf_tuple_dproj:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n" and w: "wf_tuple n (set cs) x"
  shows "dwf_tuple (length cs) (dproj (wide_mask n cs) x)"
proof -
  have l: "length x = n" using w by (simp add: wf_tuple_def)
  have "dproj (wide_mask n cs) x = map (\<lambda>c. x ! c) cs"
    by (rule dproj_wide_mask_eq_map_nth[OF s b l])
  moreover have "\<forall>c \<in> set cs. x ! c \<noteq> None" using w b by (auto simp: wf_tuple_def)
  ultimately show ?thesis by (auto simp: dwf_tuple_def)
qed

lemma dtable_dtabc:
  "sorted_wrt (<) cs \<Longrightarrow> \<forall>c \<in> set cs. c < n \<Longrightarrow> table n (set cs) T \<Longrightarrow> dtable cs (dtabc n cs T)"
  by (auto simp: dtable_def dtabc_def table_def dwf_tuple_dproj)

lemma dwiden_props:
  "length d = length (filter id bs) \<Longrightarrow> (\<forall>x \<in> set d. x \<noteq> None) \<Longrightarrow>
     length (dwiden bs d) = length bs \<and> (\<forall>i < length bs. (dwiden bs d ! i = None) = (\<not> bs ! i))"
  by (induct bs d rule: dwiden.induct) (auto simp: nth_Cons split: nat.splits)

lemma wf_tuple_dwiden:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n" and d: "dwf_tuple (length cs) d"
  shows "wf_tuple n (set cs) (dwiden (wide_mask n cs) d)"
proof -
  have lf: "length d = length (filter id (wide_mask n cs))"
    using d by (simp add: dwf_tuple_def length_filter_wide_mask[OF s b])
  have nn: "\<forall>x \<in> set d. x \<noteq> None" using d by (auto simp: dwf_tuple_def in_set_conv_nth)
  show ?thesis using dwiden_props[OF lf nn] nth_wide_mask[OF s] by (auto simp: wf_tuple_def)
qed

lemma table_dtabw:
  "sorted_wrt (<) cs \<Longrightarrow> \<forall>c \<in> set cs. c < n \<Longrightarrow> dtable cs D \<Longrightarrow> table n (set cs) (dtabw n cs D)"
  by (auto simp: dtabw_def dtable_def table_def wf_tuple_dwiden)

lemma dtabw_dtabc:
  assumes s: "sorted_wrt (<) cs" and t: "table n (set cs) T"
  shows "dtabw n cs (dtabc n cs T) = T"
  using dwiden_dtab[OF t]
  by (simp add: dtabw_def dtabc_eq_dtab[OF s] wide_mask_eq_join_mask[OF s])

lemma dproj_dwiden:
  "length d = length (filter id bs) \<Longrightarrow> dproj bs (dwiden bs d) = d"
  by (induct bs d rule: dwiden.induct) auto

lemma dtabc_dtabw:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n" and d: "dtable cs D"
  shows "dtabc n cs (dtabw n cs D) = D"
proof -
  have "\<And>x. x \<in> D \<Longrightarrow> dproj (wide_mask n cs) (dwiden (wide_mask n cs) x) = x"
    using d by (intro dproj_dwiden) (simp add: dtable_def dwf_tuple_def
        length_filter_wide_mask[OF s b])
  then show ?thesis unfolding dtabc_def dtabw_def image_image by (auto intro!: rev_image_eqI)
qed

subsection \<open>Narrowing a whole frame commutes with the join\<close>

definition cpos :: "cols \<Rightarrow> nat set \<Rightarrow> nat set" where
  "cpos cs L = {i. i < length cs \<and> cs ! i \<in> L}"

lemma cpos_code[code]: "cpos cs L = set (filter (\<lambda>i. cs ! i \<in> L) [0..<length cs])"
  by (auto simp: cpos_def)

lemma cpos_all: "cpos cs (set cs) = {0..<length cs}"
  by (auto simp: cpos_def)

lemma cpos_mono: "L \<subseteq> M \<Longrightarrow> cpos cs L \<subseteq> cpos cs M"
  by (auto simp: cpos_def)

lemma table_dtabc_cpos:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and sub: "L \<subseteq> set cs" and t: "table n L T"
  shows "table (length cs) (cpos cs L) (dtabc n cs T)"
proof -
  have "\<And>x. x \<in> T \<Longrightarrow> wf_tuple (length cs) (cpos cs L) (dproj (wide_mask n cs) x)"
  proof -
    fix x assume "x \<in> T"
    then have w: "wf_tuple n L x" using t by (simp add: table_def)
    then have l: "length x = n" by (simp add: wf_tuple_def)
    have e: "dproj (wide_mask n cs) x = map (\<lambda>c. x ! c) cs"
      by (rule dproj_wide_mask_eq_map_nth[OF s b l])
    have "\<And>i. i < length cs \<Longrightarrow> (x ! (cs ! i) = None) = (i \<notin> cpos cs L)"
      using w b by (auto simp: wf_tuple_def cpos_def)
    then show "wf_tuple (length cs) (cpos cs L) (dproj (wide_mask n cs) x)"
      using e by (auto simp: wf_tuple_def)
  qed
  then show ?thesis by (auto simp: table_def dtabc_def)
qed

lemma proj_tuple_dproj:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and sub: "L \<subseteq> set cs" and l: "length x = n"
  shows "proj_tuple (join_mask (length cs) (cpos cs L)) (dproj (wide_mask n cs) x)
       = dproj (wide_mask n cs) (proj_tuple (join_mask n L) x)"
proof -
  have lp: "length (proj_tuple (join_mask n L) x) = n"
    using l by (simp add: proj_tuple_alt join_mask_def)
  have rhs: "dproj (wide_mask n cs) (proj_tuple (join_mask n L) x)
      = map (\<lambda>c. if c \<in> L then x ! c else None) cs"
    unfolding dproj_wide_mask_eq_map_nth[OF s b lp]
    using l b by (auto simp: proj_tuple_join_mask_restrict restrict_def
        intro!: map_cong[OF refl])
  have d: "dproj (wide_mask n cs) x = map (\<lambda>c. x ! c) cs"
    by (rule dproj_wide_mask_eq_map_nth[OF s b l])
  have "proj_tuple (join_mask (length cs) (cpos cs L)) (dproj (wide_mask n cs) x)
      = restrict (cpos cs L) (map (\<lambda>c. x ! c) cs)"
    unfolding d by (rule proj_tuple_join_mask_restrict) simp
  also have "restrict (cpos cs L) (map (\<lambda>c. x ! c) cs)
      = map (\<lambda>c. if c \<in> L then x ! c else None) cs"
  proof (intro nth_equalityI)
    show "length (restrict (cpos cs L) (map (\<lambda>c. x ! c) cs))
        = length (map (\<lambda>c. if c \<in> L then x ! c else None) cs)" by (simp add: restrict_def)
    fix i assume "i < length (restrict (cpos cs L) (map (\<lambda>c. x ! c) cs))"
    then have i: "i < length cs" by (simp add: restrict_def)
    then show "restrict (cpos cs L) (map (\<lambda>c. x ! c) cs) ! i
        = map (\<lambda>c. if c \<in> L then x ! c else None) cs ! i"
      by (simp add: restrict_def cpos_def)
  qed
  finally show ?thesis using rhs by simp
qed

lemma dproj_inj_sub:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n" and sub: "L \<subseteq> set cs"
  shows "inj_on (dproj (wide_mask n cs)) {y. wf_tuple n L y}"
proof (rule inj_onI, clarsimp)
  fix y z assume w: "wf_tuple n L y" "wf_tuple n L z"
    and e: "dproj (wide_mask n cs) y = dproj (wide_mask n cs) z"
  have ly: "length y = n" and lz: "length z = n" using w by (simp_all add: wf_tuple_def)
  have "map (\<lambda>c. y ! c) cs = map (\<lambda>c. z ! c) cs"
    using e dproj_wide_mask_eq_map_nth[OF s b ly] dproj_wide_mask_eq_map_nth[OF s b lz] by simp
  then have agree: "\<And>c. c \<in> set cs \<Longrightarrow> y ! c = z ! c"
    by (auto simp: in_set_conv_nth dest!: arg_cong[where f = "\<lambda>l. l ! _"])
  have "\<And>i. i < n \<Longrightarrow> y ! i = z ! i"
  proof -
    fix i assume i: "i < n"
    show "y ! i = z ! i"
    proof (cases "i \<in> set cs")
      case True then show ?thesis by (rule agree)
    next
      case False
      then have "i \<notin> L" using sub by auto
      then show ?thesis using w i by (auto simp: wf_tuple_def)
    qed
  qed
  then show "y = z" using ly lz by (intro nth_equalityI) auto
qed

lemma dtabc_join_frame:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and sub: "L \<subseteq> A" and subA: "A \<subseteq> set cs"
    and t1: "table n A T" and t2: "table n L T'"
  shows "dtabc n cs (join T pos T') = join (dtabc n cs T) pos (dtabc n cs T')"
proof -
  have sub': "L \<subseteq> set cs" using sub subA by auto
  have j1: "join T pos T' = {a \<in> T. (proj_tuple (join_mask n L) a \<in> T') = pos}"
    using join_sub[OF sub t2 t1] by (simp add: proj_tuple_in_join_def join_cond_eq)
  have t1': "table (length cs) (cpos cs A) (dtabc n cs T)"
    by (rule table_dtabc_cpos[OF s b subA t1])
  have t2': "table (length cs) (cpos cs L) (dtabc n cs T')"
    by (rule table_dtabc_cpos[OF s b sub' t2])
  have j2: "join (dtabc n cs T) pos (dtabc n cs T')
      = {d \<in> dtabc n cs T. (proj_tuple (join_mask (length cs) (cpos cs L)) d \<in> dtabc n cs T') = pos}"
    using join_sub[OF cpos_mono[OF sub] t2' t1']
    by (simp add: proj_tuple_in_join_def join_cond_eq)
  have key: "\<And>a. a \<in> T \<Longrightarrow>
      (proj_tuple (join_mask (length cs) (cpos cs L)) (dproj (wide_mask n cs) a) \<in> dtabc n cs T')
        = (proj_tuple (join_mask n L) a \<in> T')"
  proof -
    fix a assume "a \<in> T"
    then have w: "wf_tuple n A a" using t1 by (simp add: table_def)
    then have l: "length a = n" by (simp add: wf_tuple_def)
    have wp: "wf_tuple n L (proj_tuple (join_mask n L) a)"
      using wf_tuple_proj_tuple[OF w sub] .
    show "(proj_tuple (join_mask (length cs) (cpos cs L)) (dproj (wide_mask n cs) a) \<in> dtabc n cs T')
        = (proj_tuple (join_mask n L) a \<in> T')"
      unfolding proj_tuple_dproj[OF s b sub' l] dtabc_def
      using dproj_inj_sub[OF s b sub'] wp t2 by (auto simp: table_def inj_on_def)
  qed
  have "dtabc n cs {a \<in> T. (proj_tuple (join_mask n L) a \<in> T') = pos}
      = {d \<in> dtabc n cs T. (proj_tuple (join_mask (length cs) (cpos cs L)) d \<in> dtabc n cs T') = pos}"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> dtabc n cs {a \<in> T. (proj_tuple (join_mask n L) a \<in> T') = pos}"
    then obtain a where a: "a \<in> T" "(proj_tuple (join_mask n L) a \<in> T') = pos"
      "d = dproj (wide_mask n cs) a" unfolding dtabc_def by auto
    then show "d \<in> {d \<in> dtabc n cs T.
        (proj_tuple (join_mask (length cs) (cpos cs L)) d \<in> dtabc n cs T') = pos}"
      using key[OF a(1)] by (auto simp: dtabc_def)
  next
    fix d assume d: "d \<in> {d \<in> dtabc n cs T.
        (proj_tuple (join_mask (length cs) (cpos cs L)) d \<in> dtabc n cs T') = pos}"
    then obtain a where a: "a \<in> T" "d = dproj (wide_mask n cs) a"
      unfolding dtabc_def by auto
    then show "d \<in> dtabc n cs {a \<in> T. (proj_tuple (join_mask n L) a \<in> T') = pos}"
      using d key[OF a(1)] unfolding dtabc_def by auto
  qed
  then show ?thesis unfolding j1 j2 .
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

lemma set_cols_eqI:
  assumes f: "finite A" and s: "sorted_wrt (<) xs" and e: "set xs = A"
  shows "xs = set_cols A"
proof -
  have x: "sorted xs" "distinct xs" using s by (simp_all add: strict_sorted_iff)
  have y: "sorted (set_cols A)" "distinct (set_cols A)"
    using set_cols(1)[OF f] by (simp_all add: strict_sorted_iff)
  show ?thesis using x y e set_cols(2)[OF f]
    by (simp add: sorted_distinct_set_unique)
qed

lemma set_cols_empty: "set_cols {} = []"
  by (rule set_cols_eqI[symmetric]) simp_all

lemma set_cols_singleton: "set_cols {x} = [x]"
  by (rule set_cols_eqI[symmetric]) simp_all

lemma set_cols_upt: "set_cols {0..<m} = [0..<m]"
  by (rule set_cols_eqI[symmetric]) (simp_all add: strict_sorted_iff)

subsection \<open>Narrowing at the boundary with the unmodified evaluator\<close>

definition all_true :: "bool list \<Rightarrow> bool" where
  "all_true bs = list_all id bs"

lemma dproj_all_true: "all_true bs \<Longrightarrow> length xs = length bs \<Longrightarrow> dproj bs xs = xs"
  by (induct bs xs rule: dproj.induct) (auto simp: all_true_def)

definition dnarrow :: "bool list \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
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

section \<open>The temporal operators at a re-indexed frame\<close>

text \<open>
  The @{locale msaux} and @{locale muaux} specifications are stated over an abstract auxiliary
  list of timestamped tables, and everything they do to it is a join, a union, or a filter on
  timestamps.  None of those reads a tuple position except the join, and the join commutes with
  narrowing by @{thm [source] dtabc_join_frame}.  So the verified structures can be run unchanged at a
  frame whose width is the number of columns, on narrowed tables -- which is what the theorems of
  this section say, one per operation of the two locales.
\<close>

definition dargs :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> args" where
  "dargs cs_R cs_L args = init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
     {0..<length cs_R} (args_pos args) None"

lemma dargs_simps[simp]:
  "args_ivl (dargs cs_R cs_L args) = args_ivl args"
  "args_n (dargs cs_R cs_L args) = length cs_R"
  "args_L (dargs cs_R cs_L args) = cpos cs_R (set cs_L)"
  "args_R (dargs cs_R cs_L args) = {0..<length cs_R}"
  "args_pos (dargs cs_R cs_L args) = args_pos args"
  "args_agg (dargs cs_R cs_L args) = None"
  by (simp_all add: dargs_def init_args_def)

lemma dargs_L_R: "set cs_L \<subseteq> set cs_R \<Longrightarrow>
    args_L (dargs cs_R cs_L args) \<subseteq> args_R (dargs cs_R cs_L args)"
  by (auto simp: cpos_def)

lemma dtabc_empty[simp]: "dtabc n cs {} = {}"
  by (simp add: dtabc_def)

lemma dtabc_Un_img: "dtabc n cs (A \<union> B) = dtabc n cs A \<union> dtabc n cs B"
  by (simp add: dtabc_def image_Un)

lemma eval_args_agg_None[simp]: "args_agg args = None \<Longrightarrow> eval_args_agg args X = X"
  by (simp add: eval_args_agg_def)

subsection \<open>The Since structure's auxiliary list\<close>

definition dauxlist :: "nat \<Rightarrow> cols \<Rightarrow> (ts \<times> 'b list set) list \<Rightarrow> (ts \<times> 'b list set) list" where
  "dauxlist n cs aux = map (\<lambda>(t, rel). (t, dtabc n cs rel)) aux"

lemma dauxlist_filter:
  "dauxlist n cs (filter (\<lambda>(t, rel). P t) aux) = filter (\<lambda>(t, rel). P t) (dauxlist n cs aux)"
  by (induct aux) (auto simp: dauxlist_def)

lemma dauxlist_join:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n" and sub: "L \<subseteq> set cs"
    and wf: "\<forall>(t, rel) \<in> set aux. table n (set cs) rel" and t1: "table n L rel1"
  shows "dauxlist n cs (map (\<lambda>(t, rel). (t, join rel pos rel1)) aux)
       = map (\<lambda>(t, rel). (t, join rel pos (dtabc n cs rel1))) (dauxlist n cs aux)"
  using wf by (induct aux)
    (auto simp: dauxlist_def dtabc_join_frame[OF s b sub subset_refl _ t1])

lemma dauxlist_add_new_table:
  "dauxlist n cs (case aux of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # aux)
   = (case dauxlist n cs aux of [] \<Rightarrow> [(cur, dtabc n cs rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc n cs rel2) # r
                         else (cur, dtabc n cs rel2) # dauxlist n cs aux)"
  by (cases aux) (auto simp: dauxlist_def dtabc_Un_img)

lemma dtabc_result:
  assumes "\<forall>(t, rel) \<in> set aux. table n (set cs) rel"
  shows "dtabc n cs (foldr (\<union>) [rel. (t, rel) \<leftarrow> aux, P t] {})
       = foldr (\<union>) [rel. (t, rel) \<leftarrow> dauxlist n cs aux, P t] {}"
  using assms by (induct aux) (auto simp: dauxlist_def dtabc_Un_img)

lemma dauxlist_wf_filter:
  "\<forall>(t, rel) \<in> set aux. table n (set cs) rel \<Longrightarrow>
     \<forall>(t, rel) \<in> set (filter (\<lambda>(t, rel). P t) aux). table n (set cs) rel"
  by auto

lemma dauxlist_wf_join:
  assumes "\<forall>(t, rel) \<in> set aux. table n (set cs) rel" and "L \<subseteq> set cs" and "table n L rel1"
  shows "\<forall>(t, rel) \<in> set (map (\<lambda>(t, rel). (t, join rel pos rel1)) aux). table n (set cs) rel"
  using assms by (fastforce intro: join_table[of n "set cs" _ L rel1 pos])

lemma dauxlist_wf_add_new_table:
  assumes "\<forall>(t, rel) \<in> set aux. table n (set cs) rel" and "table n (set cs) rel2"
  shows "\<forall>(t, rel) \<in> set (case aux of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # aux).
         table n (set cs) rel"
  using assms by (cases aux) (auto simp: table_def)

subsection \<open>The Until structure's auxiliary list\<close>

definition dauxlist3 :: "nat \<Rightarrow> cols \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) list" where
  "dauxlist3 n cs aux = map (\<lambda>(t, a1, a2). (t, dtabc n cs a1, dtabc n cs a2)) aux"

lemma dauxlist3_update_until:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n" and sub: "L \<subseteq> set cs"
    and wf: "\<forall>(t, a1, a2) \<in> set aux. table n L a1 \<and> table n (set cs) a2"
    and t1: "table n L rel1" and t2: "table n (set cs) rel2"
    and iv: "args_ivl args' = args_ivl args" and po: "args_pos args' = args_pos args"
  shows "dauxlist3 n cs (update_until args rel1 rel2 nt aux)
       = update_until args' (dtabc n cs rel1) (dtabc n cs rel2) nt (dauxlist3 n cs aux)"
  using wf
  by (induct aux)
    (auto simp: dauxlist3_def update_until_def iv po empty_table_def dtabc_Un_img
       dtabc_join_frame[OF s b subset_refl sub _ t1]
       dtabc_join_frame[OF s b sub subset_refl t2])

lemma dauxlist3_eval_until:
  "eval_until I nt aux = (res, aux') \<Longrightarrow>
     eval_until I nt (dauxlist3 n cs aux) = (map (dtabc n cs) res, dauxlist3 n cs aux')"
  by (induct I nt aux arbitrary: res aux' rule: eval_until.induct)
    (auto simp: dauxlist3_def split: if_splits prod.splits)

lemma table_join_same: "table n A X \<Longrightarrow> table n A Y \<Longrightarrow> table n A (join X b Y)"
  by (rule join_table[of n A X A Y b A]) auto

lemma table_join_sub: "table n A X \<Longrightarrow> table n B Y \<Longrightarrow> B \<subseteq> A \<Longrightarrow> table n A (join X b Y)"
  by (rule join_table[of n A X B Y b A]) auto

lemma table_Un: "table n A X \<Longrightarrow> table n A Y \<Longrightarrow> table n A (X \<union> Y)"
  by (auto simp: table_def)

lemma table_empty[simp]: "table n A empty_table"
  by (simp add: table_def empty_table_def)

lemma dauxlist3_wf_update_until:
  assumes wf: "\<forall>(t, a1, a2) \<in> set aux. table n L a1 \<and> table n (set cs) a2"
    and sub: "L \<subseteq> set cs" and t1: "table n L rel1" and t2: "table n (set cs) rel2"
  shows "\<forall>(t, a1, a2) \<in> set (update_until args rel1 rel2 nt aux).
      table n L a1 \<and> table n (set cs) a2"
proof safe
  have w: "\<And>t b1 b2. (t, b1, b2) \<in> set aux \<Longrightarrow> table n L b1 \<and> table n (set cs) b2"
    using wf by auto
  fix t a1 a2 assume m: "(t, a1, a2) \<in> set (update_until args rel1 rel2 nt aux)"
  show "table n L a1"
    using m t1 t2 by (auto simp: update_until_def dest!: w intro: table_join_same table_Un)
  show "table n (set cs) a2"
    using m t1 t2 sub
    by (auto simp: update_until_def dest!: w intro!: table_Un intro: table_join_sub)
qed

section \<open>Buffers of narrowed tables\<close>

text \<open>
  A buffer never looks inside a tuple: it lines up the tables the operands produce and hands
  matching pairs to the node's operation.  So a buffer of narrowed tables behaves as the
  narrowing of a buffer of wide ones.  These are map-fusion lemmas for the kernel's own
  list-level buffers, which is where its verified @{const meval} lives; the queue
  representation of @{theory MFODL_Monitor_Devel.Monitor_Impl} is layered on top of that by the
  kernel's own code equations, so the dense side can reuse it unchanged.
\<close>

lemma mbuf2_add_map:
  "mbuf2_add (map h xs') (map k ys') (map h xs, map k ys) = (map h (xs @ xs'), map k (ys @ ys'))"
  by simp

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
  so the morphism is a list of narrowings applied slotwise.  The step condition is relational for
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
    then show ?thesis using True RZ E1 E2 by (simp add: mbufn_take.simps)
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
      using E1 False by (simp add: mbufn_take.simps)
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

subsection \<open>The unit and empty tables\<close>

lemma dtabc_unit_table: "dtabc n [] (unit_table n) = unit_table 0"
  by (simp add: dtabc_def unit_table_def
      dproj_wide_mask_eq_map_nth[where cs="[]" and n=n and xs="replicate n None"])

text \<open>Hence a negation node, whose operand has no columns at all, only has to look at
  emptiness -- which narrowing preserves in both directions.\<close>

lemma dtabc_neg:
  "dtabc n [] (if T = empty_table then unit_table n else empty_table)
     = (if dtabc n [] T = empty_table then unit_table 0 else empty_table)"
  by (simp add: dtabc_unit_table dtabc_empty_iff empty_table_def)

subsection \<open>A frame with no empty columns\<close>

text \<open>When the column list covers the whole frame the mask is all true, so narrowing is the
  identity.  That is the case of a predicate whose arguments are exactly @{term "[0..<n]"}, which
  the kernel evaluates by handing the database's table straight through.\<close>

lemma all_true_wide_mask_full:
  assumes s: "sorted_wrt (<) cs" and e: "set cs = {0..<n}"
  shows "all_true (wide_mask n cs)"
  unfolding all_true_def list_all_length
  using nth_wide_mask[OF s] e by auto

lemma dtabc_empty_table[simp]: "dtabc n cs empty_table = empty_table"
  by (simp add: empty_table_def)

lemma dtabc_full:
  assumes s: "sorted_wrt (<) cs" and e: "set cs = {0..<n}" and t: "table n (set cs) T"
  shows "dtabc n cs T = T"
proof -
  have "\<And>x. x \<in> T \<Longrightarrow> dproj (wide_mask n cs) x = x"
    using t all_true_wide_mask_full[OF s e]
    by (auto simp: table_def wf_tuple_def intro!: dproj_all_true)
  then show ?thesis unfolding dtabc_def by (auto intro!: rev_image_eqI)
qed

lemma dtabc_upt: "table n {0..<n} T \<Longrightarrow> dtabc n [0..<n] T = T"
  by (rule dtabc_full) auto

subsection \<open>Leftovers and additions of the multi-way buffer\<close>

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

subsection \<open>The multi-way join as one function of the operand list\<close>

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
  by (simp add: zip_append)

subsection \<open>Leftovers of the shift buffer\<close>

lemma mprev_next_sub: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow> set xs' \<subseteq> set xs"
  by (induct I xs ts arbitrary: ys xs' ts' rule: mprev_next.induct)
    (auto split: prod.splits)

subsection \<open>The multi-way join the monitor actually runs\<close>

text \<open>@{const mmulti_join} chooses between the generic join and the pairwise one; both have the
  same membership characterisation as @{const mmulti_join'}, which is what @{thm
  dmulti_join_dtabc} is stated over.  The pairwise one needs the negated conjuncts' columns to be
  covered, which holds for every safe formula.\<close>

lemma mmulti_join_eq_mmulti_join':
  assumes ne: "A_pos \<noteq> []"
    and la: "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) L"
    and sub: "\<Union>(set A_neg) \<subseteq> \<Union>(set A_pos)"
  shows "mmulti_join n A_pos A_neg L = mmulti_join' A_pos A_neg L"
proof (cases use_generic_join)
  case True
  have "mmulti_join n A_pos A_neg L = mmulti_join_gen n A_pos A_neg L"
    by (simp only: mmulti_join.simps True if_True)
  also have "\<dots> = mmulti_join' A_pos A_neg L" by (rule mmulti_join_gen_link[OF ne la])
  finally show ?thesis .
next
  case False
  have "mmulti_join n A_pos A_neg L = mmulti_join_pw n A_pos A_neg L"
    by (simp only: mmulti_join.simps False if_False)
  also have "\<dots> = mmulti_join' A_pos A_neg L"
    by (rule set_eqI)
      (simp only: mmulti_join_pw_correct[OF ne la sub] mmulti_join'_correct[OF ne la])
  finally show ?thesis .
qed

theorem dmulti_join_eq:
  assumes s0: "sorted_wrt (<) c0" and b0: "\<forall>d \<in> set c0. d < n"
    and t0: "table n (set c0) T0" and f0: "finite T0"
    and pos: "list_all2 (wf_operand n) css Us"
    and neg: "list_all2 (wf_operand n) nss Vs"
    and sub: "\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css)"
  shows "dmulti_join (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
           (map2 (dtabc n) (c0 # css @ nss) ((T0 # Us) @ Vs))
       = dtabc n (dands_cols c0 css)
           (mmulti_join n (set c0 # map set css) (map set nss) ((T0 # Us) @ Vs))"
proof -
  have lp: "length css = length Us" using pos by (rule list_all2_lengthD)
  have ln: "length nss = length Vs" using neg by (rule list_all2_lengthD)
  have m: "map2 (dtabc n) (c0 # css @ nss) ((T0 # Us) @ Vs)
      = dtabc n c0 T0 # (map2 (dtabc n) css Us @ map2 (dtabc n) nss Vs)"
    by (simp add: map2_append[OF lp])
  have t1: "take (length (dands_plans c0 css))
      (map2 (dtabc n) css Us @ map2 (dtabc n) nss Vs) = map2 (dtabc n) css Us"
    using lp by simp
  have t2: "drop (length (dands_plans c0 css))
      (map2 (dtabc n) css Us @ map2 (dtabc n) nss Vs) = map2 (dtabc n) nss Vs"
    using lp by simp
  have "dmulti_join (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
          (map2 (dtabc n) (c0 # css @ nss) ((T0 # Us) @ Vs))
      = dands_neg (dands_plans (dands_cols c0 css) nss)
          (dands_pos (dands_plans c0 css) (dtabc n c0 T0) (map2 (dtabc n) css Us))
          (map2 (dtabc n) nss Vs)"
    unfolding dmulti_join_def m by (simp add: t1 t2 lp)
  also have "\<dots> = dtabc n (dands_cols c0 css)
      (mmulti_join' (set c0 # map set css) (map set nss) ((T0 # Us) @ Vs))"
    by (rule dmulti_join_dtabc[OF s0 b0 t0 f0 pos neg sub])
  also have "mmulti_join' (set c0 # map set css) (map set nss) ((T0 # Us) @ Vs)
      = mmulti_join n (set c0 # map set css) (map set nss) ((T0 # Us) @ Vs)"
  proof -
    have la: "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
        ((set c0 # map set css) @ map set nss) ((T0 # Us) @ Vs)"
      using t0 b0 list_all2_wf_of_operand[OF pos] list_all2_wf_of_operand[OF neg]
      by (simp add: wf_set_def list_all2_appendI)
    have su: "\<Union>(set (map set nss)) \<subseteq> \<Union>(set (set c0 # map set css))"
      using sub by (auto simp: set_dands_cols)
    show ?thesis by (rule mmulti_join_eq_mmulti_join'[OF _ la su, symmetric]) simp
  qed
  finally show ?thesis .
qed

section \<open>Comparisons on short tuples\<close>

text \<open>
  A constraint node only filters; it never changes a tuple.  Reindexing its two terms against
  the node's column list makes the filter read the short tuple at the position the column
  occupies there, which by @{thm meval_trm_reindex} evaluates to the same value.  Filtering
  commutes with an image without any injectivity, so the narrowing passes through.
\<close>

definition reindex_constraint ::
    "cols \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow>
     Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm" where
  "reindex_constraint cs conf = (case conf of (t1, p, c, t2) \<Rightarrow>
     (reindex_trm cs t1, p, c, reindex_trm cs t2))"

lemma eval_constraint_reindex:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and fv1: "Formula.fv_trm t1 \<subseteq> set cs" and fv2: "Formula.fv_trm t2 \<subseteq> set cs"
    and t: "table n (set cs) T"
  shows "dtabc n cs (Set.filter (eval_constraint (t1, p, c, t2)) T)
       = Set.filter (eval_constraint (reindex_constraint cs (t1, p, c, t2))) (dtabc n cs T)"
proof -
  have pt: "\<And>x. x \<in> T \<Longrightarrow>
      eval_constraint (reindex_constraint cs (t1, p, c, t2)) (dproj (wide_mask n cs) x)
        = eval_constraint (t1, p, c, t2) x"
  proof -
    fix x assume "x \<in> T"
    then have "wf_tuple n (set cs) x" using t by (simp add: table_def)
    then have l: "length x = n" by (simp add: wf_tuple_def)
    have d: "dproj (wide_mask n cs) x = map (\<lambda>c. x ! c) cs"
      by (rule dproj_wide_mask_eq_map_nth[OF s b l])
    show "eval_constraint (reindex_constraint cs (t1, p, c, t2)) (dproj (wide_mask n cs) x)
        = eval_constraint (t1, p, c, t2) x"
      unfolding reindex_constraint_def d
      by (simp add: meval_trm_reindex[OF fv1] meval_trm_reindex[OF fv2])
  qed
  show ?thesis unfolding dtabc_def using pt by auto
qed


section \<open>Embedding a short tuple in a wider short frame\<close>

text \<open>
  A Since structure joins its left operand into the running tables, so the left operand has to
  live in the same frame as the right one: at the dense frame, that is tuples of width
  @{term "length cs_R"} with holes outside the left columns' positions.  The left operand's own
  narrowing is at its own column list, so it has to be embedded first.  The plan is computed once
  when the formula is compiled.
\<close>

definition emb_plan :: "cols \<Rightarrow> cols \<Rightarrow> nat option list" where
  "emb_plan cs_R cs_L = map (\<lambda>c. if c \<in> set cs_L then Some (col_pos cs_L c) else None) cs_R"

definition dembed1 :: "nat option list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "dembed1 p d = map (\<lambda>q. case q of None \<Rightarrow> None | Some i \<Rightarrow> d ! i) p"

definition dembed :: "cols \<Rightarrow> cols \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "dembed cs_R cs_L D = dembed1 (emb_plan cs_R cs_L) ` D"

text \<open>The node stores the plan, not the two column lists.\<close>

definition dembedp :: "nat option list \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "dembedp p D = dembed1 p ` D"

lemma dembedp_emb_plan: "dembedp (emb_plan cs_R cs_L) D = dembed cs_R cs_L D"
  by (simp add: dembedp_def dembed_def)

lemma dembed1_dproj:
  assumes s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and b_R: "\<forall>c \<in> set cs_R. c < n" and b_L: "\<forall>c \<in> set cs_L. c < n"
    and w: "wf_tuple n (set cs_L) x"
  shows "dembed1 (emb_plan cs_R cs_L) (dproj (wide_mask n cs_L) x) = dproj (wide_mask n cs_R) x"
proof -
  have l: "length x = n" using w by (simp add: wf_tuple_def)
  have dL: "dproj (wide_mask n cs_L) x = map (\<lambda>c. x ! c) cs_L"
    by (rule dproj_wide_mask_eq_map_nth[OF s_L b_L l])
  have dR: "dproj (wide_mask n cs_R) x = map (\<lambda>c. x ! c) cs_R"
    by (rule dproj_wide_mask_eq_map_nth[OF s_R b_R l])
  have pt: "\<And>c. c \<in> set cs_R \<Longrightarrow>
      (case (if c \<in> set cs_L then Some (col_pos cs_L c) else None) of
         None \<Rightarrow> None | Some i \<Rightarrow> map (\<lambda>c. x ! c) cs_L ! i) = x ! c"
  proof -
    fix c assume c: "c \<in> set cs_R"
    show "(case (if c \<in> set cs_L then Some (col_pos cs_L c) else None) of
        None \<Rightarrow> None | Some i \<Rightarrow> map (\<lambda>c. x ! c) cs_L ! i) = x ! c"
    proof (cases "c \<in> set cs_L")
      case True
      then show ?thesis by (simp add: col_pos_nth)
    next
      case False
      have "x ! c = None" using w b_R c False by (simp add: wf_tuple_def)
      then show ?thesis using False by simp
    qed
  qed
  show ?thesis unfolding dembed1_def emb_plan_def dL dR map_map
    by (rule map_cong[OF refl]) (simp add: o_def pt)
qed

theorem dembed_dtabc:
  assumes s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and b_R: "\<forall>c \<in> set cs_R. c < n" and b_L: "\<forall>c \<in> set cs_L. c < n"
    and t: "table n (set cs_L) T"
  shows "dembed cs_R cs_L (dtabc n cs_L T) = dtabc n cs_R T"
proof -
  have pt: "\<And>x. x \<in> T \<Longrightarrow>
      dembed1 (emb_plan cs_R cs_L) (dproj (wide_mask n cs_L) x) = dproj (wide_mask n cs_R) x"
    using t by (intro dembed1_dproj[OF s_R s_L b_R b_L]) (simp add: table_def)
  show ?thesis unfolding dembed_def dtabc_def image_image
    by (rule image_cong[OF refl]) (rule pt)
qed

corollary dembedp_dtabc:
  assumes "sorted_wrt (<) cs_R" and "sorted_wrt (<) cs_L"
    and "\<forall>c \<in> set cs_R. c < n" and "\<forall>c \<in> set cs_L. c < n"
    and "table n (set cs_L) T"
  shows "dembedp (emb_plan cs_R cs_L) (dtabc n cs_L T) = dtabc n cs_R T"
  unfolding dembedp_emb_plan by (rule dembed_dtabc[OF assms])

text \<open>Both narrowings land where the structure at @{const dargs} expects them: by
  @{thm [source] table_dtabc_cpos} the right operand's in the full dense frame
  (@{term "cpos cs (set cs) = {0..<length cs}"}, which is @{thm [source] cpos_all}), and the left
  operand's, after the embedding above, in the positions its columns occupy there.\<close>


section \<open>The assignment, the time point and the timestamp\<close>

text \<open>
  Three of the kernel's nodes produce or extend a table by arithmetic on one tuple at a time,
  and each has a short counterpart that does the same work on a tuple that is as long as the
  node's columns rather than as long as the frame.
\<close>

subsection \<open>Assigning a term to a fresh column\<close>

text \<open>
  The kernel's assignment fills the hole at the assigned variable's position:
  @{thm eval_assignment.simps}.  A short tuple has no hole to fill, so the value is
  \<^emph>\<open>inserted\<close> at the position the new column occupies in the merged column list --
  the same insertion the aggregation's output does, at the same @{const ins_pos}.
\<close>

definition dassign1 :: "nat \<Rightarrow> Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> event_data tuple" where
  "dassign1 p t d = take p d @ Some (meval_trm t d) # drop p d"

definition dassign :: "nat \<Rightarrow> Formula.trm \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dassign p t D = dassign1 p t ` D"

theorem dassign_eval_assignment:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and y: "y < n" and yn: "y \<notin> set cs"
    and fv: "Formula.fv_trm t \<subseteq> set cs" and tT: "table n (set cs) T"
  shows "dassign (ins_pos cs y) (reindex_trm cs t) (dtabc n cs T)
       = dtabc n (merge_cols cs [y]) (eval_assignment (y, t) ` T)"
proof -
  let ?p = "ins_pos cs y"
  let ?cs' = "merge_cols cs [y]"
  have cs': "?cs' = take ?p cs @ y # drop ?p cs" by (rule merge_cols_single[OF s yn])
  have s': "sorted_wrt (<) ?cs'" using s by (intro sorted_merge_cols) simp_all
  have b': "\<forall>c \<in> set ?cs'. c < n" using b y by (simp add: set_merge_cols)
  have key: "\<And>x. x \<in> T \<Longrightarrow>
      dassign1 ?p (reindex_trm cs t) (dproj (wide_mask n cs) x)
        = dproj (wide_mask n ?cs') (eval_assignment (y, t) x)"
  proof -
    fix x assume x: "x \<in> T"
    have len: "length x = n" using tT x by (auto simp: table_def wf_tuple_def)
    let ?v = "Some (meval_trm t x)"
    let ?x' = "x[y := ?v]"
    have len': "length ?x' = n" using len by simp
    have d: "dproj (wide_mask n cs) x = map (\<lambda>c. x ! c) cs"
      by (rule dproj_wide_mask_eq_map_nth[OF s b len])
    have ev: "meval_trm (reindex_trm cs t) (map (\<lambda>c. x ! c) cs) = meval_trm t x"
      by (rule meval_trm_reindex[OF fv])
    have d': "dproj (wide_mask n ?cs') ?x' = map (\<lambda>c. ?x' ! c) ?cs'"
      by (rule dproj_wide_mask_eq_map_nth[OF s' b' len'])
    have nth_cs: "\<And>c. c \<in> set cs \<Longrightarrow> ?x' ! c = x ! c"
      using yn by (metis nth_list_update_neq)
    have nth_y: "?x' ! y = ?v" using y len by simp
    have mm: "map (\<lambda>c. ?x' ! c) ?cs'
        = map (\<lambda>c. x ! c) (take ?p cs) @ ?v # map (\<lambda>c. x ! c) (drop ?p cs)"
      unfolding cs' using nth_cs nth_y
      by (auto intro!: map_cong dest: in_set_takeD in_set_dropD)
    show "dassign1 ?p (reindex_trm cs t) (dproj (wide_mask n cs) x)
        = dproj (wide_mask n ?cs') (eval_assignment (y, t) x)"
      unfolding eval_assignment.simps d' mm dassign1_def d ev
      by (simp add: take_map drop_map)
  qed
  show ?thesis unfolding dassign_def dtabc_def image_image
    using key by (auto intro!: image_cong)
qed

lemma finite_dassign: "finite D \<Longrightarrow> finite (dassign p t D)"
  by (simp add: dassign_def)

text \<open>The operand's column list is the node's without the assigned column, and putting the
  latter back is the merge the theorem above asks for.\<close>

definition rem_col :: "cols \<Rightarrow> nat \<Rightarrow> cols" where
  "rem_col cs y = filter (\<lambda>c. c \<noteq> y) cs"

lemma sorted_rem_col: "sorted_wrt (<) cs \<Longrightarrow> sorted_wrt (<) (rem_col cs y)"
  unfolding rem_col_def by (induct cs) auto

lemma set_rem_col: "set (rem_col cs y) = set cs - {y}"
  unfolding rem_col_def by auto

lemma rem_col_set_cols:
  "finite A \<Longrightarrow> y \<notin> A \<Longrightarrow> rem_col (set_cols (Set.insert y A)) y = set_cols A"
  by (rule set_cols_eqI)
    (auto simp: set_rem_col sorted_rem_col set_cols(1)[of "Set.insert y A"]
      set_cols(2)[of "Set.insert y A"])

lemma merge_rem_col:
  "sorted_wrt (<) cs \<Longrightarrow> y \<in> set cs \<Longrightarrow> merge_cols (rem_col cs y) [y] = cs"
  unfolding rem_col_def
proof (induct cs)
  case (Cons c cs)
  note IH = Cons(1) and srt = Cons(2) and mem = Cons(3)
  show ?case
  proof (cases "c = y")
    case True
    then have ny: "y \<notin> set cs" using srt by auto
    then have f: "filter (\<lambda>c. c \<noteq> y) cs = cs" by (auto simp: filter_id_conv)
    have "merge_cols cs [y] = y # cs"
    proof (cases cs)
      case Nil
      then show ?thesis by simp
    next
      case (Cons d ds)
      then have "y < d" using srt True by auto
      then show ?thesis using Cons by (simp add: merge_cols_Nil2)
    qed
    then show ?thesis using True f by simp
  next
    case False
    then have ymem: "y \<in> set cs" using mem by auto
    then have cy: "c < y" using srt by auto
    show ?thesis using IH[OF _ ymem] srt cy False by simp
  qed
qed simp

subsection \<open>The time point and the timestamp\<close>

text \<open>
  The two nodes that turn a number into a table produce either a one-column table holding that
  number or a zero-column truth value, so their short forms are @{term "{[Some x]}"} and the
  short unit or empty table -- no frame-wide tuple is built at all.
\<close>

fun dmtrm :: "mtrm \<Rightarrow> event_data \<Rightarrow> event_data table" where
  "dmtrm (MVar v) x = {[Some x]}"
| "dmtrm (MConst c) x = (if c = x then unit_table 0 else empty_table)"

definition mtrm_dcols :: "mtrm \<Rightarrow> cols" where
  "mtrm_dcols mt = (case mt of MVar v \<Rightarrow> [v] | MConst c \<Rightarrow> [])"

lemma sorted_mtrm_dcols: "sorted_wrt (<) (mtrm_dcols mt)"
  by (cases mt) (simp_all add: mtrm_dcols_def)

lemma finite_dmtrm: "finite (dmtrm mt x)"
  by (cases mt) (simp_all add: unit_table_def empty_table_def)

theorem dtabc_eval_mtrm:
  assumes b: "\<forall>c \<in> set (mtrm_dcols mt). c < n"
  shows "dtabc n (mtrm_dcols mt) (eval_mtrm n mt x) = dmtrm mt x"
proof (cases mt)
  case (MVar v)
  have v: "v < n" using b unfolding MVar mtrm_dcols_def by simp
  let ?tab = "Table.tabulate (\<lambda>j. if v = j then Some x else None) 0 n"
  have len: "length ?tab = n" by simp
  have "dproj (wide_mask n [v]) ?tab = map (\<lambda>c. ?tab ! c) [v]"
    by (rule dproj_wide_mask_eq_map_nth) (use v len in simp_all)
  then show ?thesis
    unfolding MVar mtrm_dcols_def dtabc_def by (simp add: singleton_table_def v)
next
  case (MConst c)
  show ?thesis
  proof (cases "c = x")
    case True
    then show ?thesis unfolding MConst mtrm_dcols_def by (simp add: dtabc_unit_table)
  next
    case False
    then show ?thesis unfolding MConst mtrm_dcols_def
      by (simp add: dtabc_def empty_table_def)
  qed
qed


section \<open>The verified Since structure at the dense frame\<close>

text \<open>
  Putting the pieces together: the invariant the dense Since node carries is that the verified
  @{typ mmasaux}, run at @{const dargs}, is valid for the narrowing of the auxiliary list the wide
  one is valid for.  Each of the structure's four operations preserves it, and the result it
  computes is the narrowing of the result the wide one computes.  The aggregation is the one thing
  that does not transport -- @{const dargs} has no aggregation -- so a Since with an aggregation
  pushed into it stays a wide node.
\<close>

definition dsaux :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow>
    (ts \<times> event_data table) list \<Rightarrow> bool" where
  "dsaux n cs_R cs_L args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel) \<and>
     valid_mmasaux (dargs cs_R cs_L args) cur daux (dauxlist n cs_R auxlist)"

lemma dsaux_init:
  assumes sub: "set cs_L \<subseteq> set cs_R"
  shows "dsaux n cs_R cs_L args 0 (init_mmasaux (dargs cs_R cs_L args)) []"
proof -
  have "valid_mmasaux (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
      {0..<length cs_R} (args_pos args) None) 0
      (init_mmasaux (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
        {0..<length cs_R} (args_pos args) None)) []"
    by (rule default_mmasaux.valid_init_msaux)
      (use sub in \<open>auto simp: cpos_def valid_aggargs_def\<close>)
  then show ?thesis by (simp add: dsaux_def dargs_def dauxlist_def)
qed

lemma dsaux_add_new_ts:
  assumes v: "dsaux n cs_R cs_L args cur daux auxlist" and nt: "cur \<le> nt"
  shows "dsaux n cs_R cs_L args nt (add_new_ts_mmasaux (dargs cs_R cs_L args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_mmasaux (dargs cs_R cs_L args) cur daux (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux_def)
  have "valid_mmasaux (dargs cs_R cs_L args) nt
      (add_new_ts_mmasaux (dargs cs_R cs_L args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl (dargs cs_R cs_L args)) (nt - t))
        (dauxlist n cs_R auxlist))"
    by (rule default_mmasaux.valid_add_new_ts_msaux[OF d nt])
  then show ?thesis using w by (simp add: dsaux_def dauxlist_filter)
qed

lemma dsaux_join:
  assumes v: "dsaux n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and b_R: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R" and t1: "table n (set cs_L) rel1"
  shows "dsaux n cs_R cs_L args cur
      (gc_join_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R rel1) daux)
      (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_mmasaux (dargs cs_R cs_L args) cur daux (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux_def)
  have tt: "table (args_n (dargs cs_R cs_L args)) (args_L (dargs cs_R cs_L args))
      (dtabc n cs_R rel1)"
    by (simp add: table_dtabc_cpos[OF s_R b_R sub t1])
  have "valid_mmasaux (dargs cs_R cs_L args) cur
      (gc_join_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R rel1) daux)
      (map (\<lambda>(t, rel). (t, join rel (args_pos (dargs cs_R cs_L args)) (dtabc n cs_R rel1)))
        (dauxlist n cs_R auxlist))"
    by (rule default_mmasaux.valid_join_msaux[OF d tt])
  then show ?thesis using w
    by (simp add: dsaux_def dauxlist_join[OF s_R b_R sub w t1]
        dauxlist_wf_join[OF w sub t1])
qed

lemma dsaux_add_new_table:
  assumes v: "dsaux n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and b_R: "\<forall>c \<in> set cs_R. c < n"
    and t2: "table n (set cs_R) rel2"
  shows "dsaux n cs_R cs_L args cur
      (add_new_table_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R rel2) daux)
      (case auxlist of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_mmasaux (dargs cs_R cs_L args) cur daux (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux_def)
  have tt: "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R rel2)"
    using table_dtabc_cpos[OF s_R b_R subset_refl t2] by (simp add: cpos_all)
  have "valid_mmasaux (dargs cs_R cs_L args) cur
      (add_new_table_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R rel2) daux)
      (case dauxlist n cs_R auxlist of [] \<Rightarrow> [(cur, dtabc n cs_R rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc n cs_R rel2) # r
                         else (cur, dtabc n cs_R rel2) # dauxlist n cs_R auxlist)"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF d tt])
  then show ?thesis using w t2
    by (simp add: dsaux_def dauxlist_add_new_table[symmetric]
        dauxlist_wf_add_new_table[OF w t2])
qed

lemma dsaux_result:
  assumes v: "dsaux n cs_R cs_L args cur daux auxlist"
  shows "result_mmasaux (dargs cs_R cs_L args) daux
      = dtabc n cs_R (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist,
          memL (args_ivl args) (cur - t)] {})"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_mmasaux (dargs cs_R cs_L args) cur daux (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux_def)
  have "result_mmasaux (dargs cs_R cs_L args) daux
      = eval_args_agg (dargs cs_R cs_L args) (foldr (\<union>)
          [rel. (t, rel) \<leftarrow> dauxlist n cs_R auxlist,
           memL (args_ivl (dargs cs_R cs_L args)) (cur - t)] {})"
    by (rule default_mmasaux.valid_result_msaux[OF d])
  then show ?thesis by (simp add: dtabc_result[OF w])
qed


section \<open>The verified Until structure at the dense frame\<close>

text \<open>
  The same argument for the Until structure.  Its auxiliary list carries two tables per time
  point -- the left operand's accumulated join and the right operand's accumulated union -- and
  both are narrowed at the right operand's column list, which is where @{const dauxlist3} puts
  them.  There are three operations rather than five, and the aggregation again does not
  transport.
\<close>

definition duaux :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> muaux_dq \<Rightarrow>
    event_data muaux \<Rightarrow> bool" where
  "duaux n cs_R cs_L args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2) \<and>
     valid_muaux_dq (dargs cs_R cs_L args) cur daux (dauxlist3 n cs_R auxlist)"

lemma duaux_init:
  assumes sub: "set cs_L \<subseteq> set cs_R"
  shows "duaux n cs_R cs_L args 0 (init_muaux_dq (dargs cs_R cs_L args)) []"
proof -
  have "valid_muaux_dq (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
      {0..<length cs_R} (args_pos args) None) 0
      (init_muaux_dq (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
        {0..<length cs_R} (args_pos args) None)) []"
    by (rule valid_init_muaux_dq) (use sub in \<open>auto simp: cpos_def\<close>)
  then show ?thesis by (simp add: duaux_def dargs_def dauxlist3_def)
qed

lemma duaux_add_new:
  assumes v: "duaux n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and b_R: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R"
    and t1: "table n (set cs_L) rel1" and t2: "table n (set cs_R) rel2"
    and nt: "cur \<le> nt"
  shows "duaux n cs_R cs_L args nt
      (add_new_muaux_dq (dargs cs_R cs_L args) (dtabc n cs_R rel1) (dtabc n cs_R rel2) nt daux)
      (update_until args rel1 rel2 nt auxlist)"
proof -
  have w: "\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2"
    and d: "valid_muaux_dq (dargs cs_R cs_L args) cur daux (dauxlist3 n cs_R auxlist)"
    using v by (auto simp: duaux_def)
  have tt1: "table (args_n (dargs cs_R cs_L args)) (args_L (dargs cs_R cs_L args))
      (dtabc n cs_R rel1)"
    by (simp add: table_dtabc_cpos[OF s_R b_R sub t1])
  have tt2: "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R rel2)"
    using table_dtabc_cpos[OF s_R b_R subset_refl t2] by (simp add: cpos_all)
  have "valid_muaux_dq (dargs cs_R cs_L args) nt
      (add_new_muaux_dq (dargs cs_R cs_L args) (dtabc n cs_R rel1) (dtabc n cs_R rel2) nt daux)
      (update_until (dargs cs_R cs_L args) (dtabc n cs_R rel1) (dtabc n cs_R rel2) nt
        (dauxlist3 n cs_R auxlist))"
    by (rule valid_add_new_muaux_dq[OF d tt1 tt2 nt])
  then show ?thesis using dauxlist3_wf_update_until[OF w sub t1 t2]
    by (simp add: duaux_def dauxlist3_update_until[OF s_R b_R sub w t1 t2, symmetric])
qed

lemma duaux_eval:
  assumes v: "duaux n cs_R cs_L args cur daux auxlist" and nt: "cur \<le> nt"
    and de: "eval_muaux_dq (dargs cs_R cs_L args) nt daux = (dres, daux')"
    and we: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
  shows "dres = map (dtabc n cs_R) res \<and> duaux n cs_R cs_L args cur daux' auxlist'"
proof -
  have w: "\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2"
    and d: "valid_muaux_dq (dargs cs_R cs_L args) cur daux (dauxlist3 n cs_R auxlist)"
    using v by (auto simp: duaux_def)
  have de': "eval_until (args_ivl (dargs cs_R cs_L args)) nt (dauxlist3 n cs_R auxlist)
      = (map (dtabc n cs_R) res, dauxlist3 n cs_R auxlist')"
    using dauxlist3_eval_until[OF we] by simp
  have vd: "valid_muaux_dq (dargs cs_R cs_L args) cur daux' (dauxlist3 n cs_R auxlist')"
    and r: "dres = map (eval_args_agg (dargs cs_R cs_L args)) (map (dtabc n cs_R) res)"
    using valid_eval_muaux_dq[OF d nt de de'] by simp_all
  have "set auxlist' \<subseteq> set auxlist"
    using eval_until_auxlist'[OF we] by (simp add: set_drop_subset)
  then show ?thesis using vd r w by (auto simp: duaux_def)
qed

section \<open>The verified Trigger structure at the dense frame\<close>

text \<open>
  The trigger's auxiliary list carries two tables per time point, like the Until's, but the
  structure reads its answer off that list rather than accumulating it, so what has to transport
  is @{const trigger_results} itself.  Its \<^emph>\<open>then\<close> branch is a set comprehension over tuples of
  the right operand's frame, and the two conditions it puts on a tuple -- membership in a stored
  right table, and a join against a stored left table -- are the two the join at @{const cpos}
  already transports.  Both are stated here on their own, because the comprehension needs them
  pointwise rather than as an image.
\<close>

lemma dtabc_in_iff:
  assumes s: "sorted_wrt (<) cs" and t: "table n (set cs) T" and w: "wf_tuple n (set cs) a"
  shows "(dproj (wide_mask n cs) a \<in> dtabc n cs T) = (a \<in> T)"
  unfolding dtabc_eq_dtab[OF s] wide_mask_eq_join_mask[OF s] by (rule dtab_in_iff[OF t w])

lemma proj_tuple_dtabc_in_iff:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n" and sub: "L \<subseteq> set cs"
    and t: "table n L T" and w: "wf_tuple n (set cs) a"
  shows "(proj_tuple (join_mask (length cs) (cpos cs L)) (dproj (wide_mask n cs) a)
            \<in> dtabc n cs T)
       = (proj_tuple (join_mask n L) a \<in> T)"
proof -
  have l: "length a = n" using w by (simp add: wf_tuple_def)
  have wp: "wf_tuple n L (proj_tuple (join_mask n L) a)" using wf_tuple_proj_tuple[OF w sub] .
  show ?thesis
    unfolding proj_tuple_dproj[OF s b sub l] dtabc_def
    using dproj_inj_sub[OF s b sub] wp t by (auto simp: table_def inj_on_def)
qed

text \<open>The comprehension, with the pattern matches and the bounded quantifier written out, so
  that the two frames can be compared position by position.\<close>

lemma trigger_results_snd:
  "snd (trigger_results args cur auxlist) =
     (if 0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist)
      then {tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
        (\<forall>i < length auxlist. mem (args_ivl args) (cur - fst (auxlist ! i)) \<longrightarrow>
           (tuple \<in> snd (snd (auxlist ! i)) \<or>
            (\<exists>j. i < j \<and> j < length auxlist \<and>
               join_cond (args_pos args) (fst (snd (auxlist ! j)))
                 (proj_tuple (join_mask (args_n args) (args_L args)) tuple))))}
      else {replicate (args_n args) None})"
  by (auto simp: Let_def case_prod_beta)

lemma length_filter_dauxlist3:
  "length (filter (\<lambda>(t, _, _). P t) (dauxlist3 n cs auxlist))
     = length (filter (\<lambda>(t, _, _). P t) auxlist)"
  by (induct auxlist) (auto simp: dauxlist3_def)

lemma nth_dauxlist3:
  "i < length auxlist \<Longrightarrow> dauxlist3 n cs auxlist ! i =
     (fst (auxlist ! i), dtabc n cs (fst (snd (auxlist ! i))),
      dtabc n cs (snd (snd (auxlist ! i))))"
  by (simp add: dauxlist3_def case_prod_beta)

text \<open>A tuple of the right operand's frame and its short form correspond one for one, in both
  directions: the short form of a well-formed tuple is a hole-free tuple of the dense frame, and
  widening a hole-free one gets the original back.\<close>

lemma wf_tuple_dproj_full:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n" and w: "wf_tuple n (set cs) a"
  shows "wf_tuple (length cs) {0..<length cs} (dproj (wide_mask n cs) a)"
proof -
  have "table (length cs) (cpos cs (set cs)) (dtabc n cs {a})"
    by (rule table_dtabc_cpos[OF s b order.refl]) (use w in \<open>simp add: table_def\<close>)
  then show ?thesis by (simp add: cpos_all dtabc_def table_def)
qed

lemma wf_tuple_dwiden_full:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and d: "wf_tuple (length cs) {0..<length cs} d"
  shows "wf_tuple n (set cs) (dwiden (wide_mask n cs) d)"
    and "dproj (wide_mask n cs) (dwiden (wide_mask n cs) d) = d"
proof -
  have dw: "dwf_tuple (length cs) d" using d by (simp add: dwf_tuple_def wf_tuple_def)
  show "wf_tuple n (set cs) (dwiden (wide_mask n cs) d)" by (rule wf_tuple_dwiden[OF s b dw])
  show "dproj (wide_mask n cs) (dwiden (wide_mask n cs) d) = d"
    by (rule dproj_dwiden) (use dw in \<open>simp add: dwf_tuple_def length_filter_wide_mask[OF s b]\<close>)
qed

text \<open>The transfer itself.  The node's interval contains zero and the structure is asked for its
  answer right after a time point was entered, so the \<^emph>\<open>else\<close> branch is out of reach; it is
  assumed away, and the caller discharges it from the update it just did.\<close>

text \<open>The unit table narrows to the unit table of the dense frame -- at the empty column list,
  to @{term "{[]}"}.  That is what makes the second branch of @{const trigger_results} transport
  like the first one, rather than having to be assumed away.\<close>

lemma dtabc_unit_table_cols:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
  shows "dtabc n cs (unit_table n) = unit_table (length cs)"
proof -
  have l: "length (replicate n None :: 'a tuple) = n" by simp
  have "dproj (wide_mask n cs) (replicate n None :: 'a tuple)
      = map (\<lambda>c. (replicate n None :: 'a tuple) ! c) cs"
    by (rule dproj_wide_mask_eq_map_nth[OF s b l])
  also have "\<dots> = replicate (length cs) None" using b by (intro nth_equalityI) auto
  finally show ?thesis by (simp add: dtabc_def unit_table_def)
qed

theorem dtabc_trigger_results:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and sub: "set cs_L \<subseteq> set cs"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs"
    and wf: "\<forall>(t, l, r) \<in> set auxlist. table n (set cs_L) l \<and> table n (set cs) r"
  shows "snd (trigger_results (dargs cs cs_L args) cur (dauxlist3 n cs auxlist))
       = dtabc n cs (snd (trigger_results args cur auxlist))"
proof -
  have len: "length (dauxlist3 n cs auxlist) = length auxlist" by (simp add: dauxlist3_def)
  have tl: "\<And>i. i < length auxlist \<Longrightarrow> table n (set cs_L) (fst (snd (auxlist ! i)))"
    using wf by (fastforce simp: case_prod_beta dest: nth_mem)
  have tr: "\<And>i. i < length auxlist \<Longrightarrow> table n (set cs) (snd (snd (auxlist ! i)))"
    using wf by (fastforce simp: case_prod_beta dest: nth_mem)
  \<comment> \<open>the two conditions the comprehension puts on a tuple, one position at a time\<close>
  have cond: "\<And>a :: event_data tuple. wf_tuple n (set cs) a \<Longrightarrow>
      (\<forall>i < length auxlist. mem (args_ivl args) (cur - fst (dauxlist3 n cs auxlist ! i)) \<longrightarrow>
         (dproj (wide_mask n cs) a \<in> snd (snd (dauxlist3 n cs auxlist ! i)) \<or>
          (\<exists>j. i < j \<and> j < length auxlist \<and>
             join_cond (args_pos args) (fst (snd (dauxlist3 n cs auxlist ! j)))
               (proj_tuple (join_mask (length cs) (cpos cs (set cs_L)))
                 (dproj (wide_mask n cs) a)))))
    = (\<forall>i < length auxlist. mem (args_ivl args) (cur - fst (auxlist ! i)) \<longrightarrow>
         (a \<in> snd (snd (auxlist ! i)) \<or>
          (\<exists>j. i < j \<and> j < length auxlist \<and>
             join_cond (args_pos args) (fst (snd (auxlist ! j)))
               (proj_tuple (join_mask n (set cs_L)) a))))"
  proof -
    fix a :: "event_data tuple" assume w: "wf_tuple n (set cs) a"
    have inR: "\<And>i. i < length auxlist \<Longrightarrow>
        (dproj (wide_mask n cs) a \<in> dtabc n cs (snd (snd (auxlist ! i))))
          = (a \<in> snd (snd (auxlist ! i)))"
      by (rule dtabc_in_iff[OF s tr w])
    have inL: "\<And>j. j < length auxlist \<Longrightarrow>
        (proj_tuple (join_mask (length cs) (cpos cs (set cs_L))) (dproj (wide_mask n cs) a)
            \<in> dtabc n cs (fst (snd (auxlist ! j))))
          = (proj_tuple (join_mask n (set cs_L)) a \<in> fst (snd (auxlist ! j)))"
      by (rule proj_tuple_dtabc_in_iff[OF s b sub tl w])
    show "(\<forall>i < length auxlist. mem (args_ivl args) (cur - fst (dauxlist3 n cs auxlist ! i)) \<longrightarrow>
         (dproj (wide_mask n cs) a \<in> snd (snd (dauxlist3 n cs auxlist ! i)) \<or>
          (\<exists>j. i < j \<and> j < length auxlist \<and>
             join_cond (args_pos args) (fst (snd (dauxlist3 n cs auxlist ! j)))
               (proj_tuple (join_mask (length cs) (cpos cs (set cs_L)))
                 (dproj (wide_mask n cs) a)))))
    = (\<forall>i < length auxlist. mem (args_ivl args) (cur - fst (auxlist ! i)) \<longrightarrow>
         (a \<in> snd (snd (auxlist ! i)) \<or>
          (\<exists>j. i < j \<and> j < length auxlist \<and>
             join_cond (args_pos args) (fst (snd (auxlist ! j)))
               (proj_tuple (join_mask n (set cs_L)) a))))"
      by (auto simp: nth_dauxlist3 join_cond_eq inR inL)
  qed
  \<comment> \<open>and the two frames a tuple can live in\<close>
  let ?S = "{a. wf_tuple n (set cs) a \<and>
      (\<forall>i < length auxlist. mem (args_ivl args) (cur - fst (auxlist ! i)) \<longrightarrow>
         (a \<in> snd (snd (auxlist ! i)) \<or>
          (\<exists>j. i < j \<and> j < length auxlist \<and>
             join_cond (args_pos args) (fst (snd (auxlist ! j)))
               (proj_tuple (join_mask n (set cs_L)) a))))}"
  let ?D = "{d. wf_tuple (length cs) {0..<length cs} d \<and>
      (\<forall>i < length auxlist. mem (args_ivl args) (cur - fst (dauxlist3 n cs auxlist ! i)) \<longrightarrow>
         (d \<in> snd (snd (dauxlist3 n cs auxlist ! i)) \<or>
          (\<exists>j. i < j \<and> j < length auxlist \<and>
             join_cond (args_pos args) (fst (snd (dauxlist3 n cs auxlist ! j)))
               (proj_tuple (join_mask (length cs) (cpos cs (set cs_L))) d))))}"
  have DS: "?D = dtabc n cs ?S"
  proof (intro set_eqI iffI)
    fix d :: "event_data tuple" assume d: "d \<in> ?D"
    then have wd: "wf_tuple (length cs) {0..<length cs} d" by simp
    have wa: "wf_tuple n (set cs) (dwiden (wide_mask n cs) d)"
      by (rule wf_tuple_dwiden_full(1)[OF s b wd])
    have pd: "dproj (wide_mask n cs) (dwiden (wide_mask n cs) d) = d"
      by (rule wf_tuple_dwiden_full(2)[OF s b wd])
    have inS: "dwiden (wide_mask n cs) d \<in> ?S"
      using d wa cond[OF wa] unfolding pd by simp
    have im: "dproj (wide_mask n cs) (dwiden (wide_mask n cs) d) \<in> dproj (wide_mask n cs) ` ?S"
      by (rule imageI[OF inS])
    show "d \<in> dtabc n cs ?S" using im[unfolded pd] by (simp add: dtabc_def)
  next
    fix d :: "event_data tuple" assume "d \<in> dtabc n cs ?S"
    then obtain a where a: "a \<in> ?S" and de: "d = dproj (wide_mask n cs) a"
      unfolding dtabc_def by auto
    have wa: "wf_tuple n (set cs) a" using a by simp
    show "d \<in> ?D" using a cond[OF wa] wf_tuple_dproj_full[OF s b wa] unfolding de by simp
  qed
  have flt: "(0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t))
        (dauxlist3 n cs auxlist)))
      = (0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist))"
    unfolding length_filter_dauxlist3 ..
  show ?thesis
  proof (cases "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist)")
    case True
    have dsimp: "snd (trigger_results (dargs cs cs_L args) cur (dauxlist3 n cs auxlist)) = ?D"
      unfolding trigger_results_snd using True flt by (simp add: len)
    have ssimp: "snd (trigger_results args cur auxlist) = ?S"
      unfolding trigger_results_snd using True by (simp add: an aL aR)
    show ?thesis unfolding dsimp ssimp by (rule DS)
  next
    \<comment> \<open>the empty window: both frames answer their own unit table, and narrowing takes one to
        the other\<close>
    case False
    have dsimp: "snd (trigger_results (dargs cs cs_L args) cur (dauxlist3 n cs auxlist))
        = unit_table (length cs)"
      unfolding trigger_results_snd using False flt by (simp add: unit_table_def)
    have ssimp: "snd (trigger_results args cur auxlist) = unit_table n"
      unfolding trigger_results_snd using False by (simp add: an unit_table_def)
    show ?thesis unfolding dsimp ssimp by (rule dtabc_unit_table_cols[OF s b, symmetric])
  qed
qed

text \<open>The structure at the dense frame, related to the kernel's through the abstract auxiliary
  list they are both valid for, exactly as for the Since and the Until.\<close>

lemma dauxlist3_filter_append:
  "dauxlist3 n cs (filter (\<lambda>(t, _). P t) auxlist @ [(nt, l, r)])
     = filter (\<lambda>(t, _). P t) (dauxlist3 n cs auxlist) @ [(nt, dtabc n cs l, dtabc n cs r)]"
  by (induct auxlist) (auto simp: dauxlist3_def)

text \<open>The trigger's buffer traversal, stepped at both frames at once.  It is
  @{thm [source] mbuf2t_take_rel_ts} without the timestamp bookkeeping: the two runs consume the
  same number of entries, because narrowing a list of tables preserves its length.\<close>

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

definition dtaux :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data mmtaux \<Rightarrow>
    event_data mtaux \<Rightarrow> bool" where
  "dtaux n cs_R cs_L args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, l, r) \<in> set auxlist. table n (set cs_L) l \<and> table n (set cs_R) r) \<and>
     valid_mmtaux (dargs cs_R cs_L args) cur daux (dauxlist3 n cs_R auxlist)"

lemma dtaux_init:
  assumes sub: "set cs_L \<subseteq> set cs_R" and m0: "mem (args_ivl args) 0"
  shows "dtaux n cs_R cs_L args 0 (init_mmtaux (dargs cs_R cs_L args)) []"
proof -
  have sub': "cpos cs_R (set cs_L) \<subseteq> {0..<length cs_R}"
    by (auto simp: cpos_def)
  have "valid_mmtaux (dargs cs_R cs_L args) 0 (init_mmtaux (dargs cs_R cs_L args)) []"
    using valid_init_mmtaux[where I = "args_ivl args" and n = "length cs_R"
        and L = "cpos cs_R (set cs_L)" and R = "{0..<length cs_R}"
        and pos = "args_pos args" and agg = None]
      m0 sub'
    by (simp add: dargs_def Let_def)
  then show ?thesis by (simp add: dtaux_def dauxlist3_def)
qed

lemma dtaux_update:
  assumes v: "dtaux n cs_R cs_L args cur daux auxlist" and nt: "cur \<le> nt"
    and s: "sorted_wrt (<) cs_R" and b: "\<forall>c \<in> set cs_R. c < n" and sub: "set cs_L \<subseteq> set cs_R"
    and tl: "table n (set cs_L) l" and tr: "table n (set cs_R) r"
  shows "dtaux n cs_R cs_L args nt
      (update_mmtaux (dargs cs_R cs_L args) nt (dtabc n cs_R l) (dtabc n cs_R r) daux)
      (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist @ [(nt, l, r)])"
proof -
  have w: "\<forall>(t, l, r) \<in> set auxlist. table n (set cs_L) l \<and> table n (set cs_R) r"
    and d: "valid_mmtaux (dargs cs_R cs_L args) cur daux (dauxlist3 n cs_R auxlist)"
    using v by (auto simp: dtaux_def)
  have tl': "table (args_n (dargs cs_R cs_L args)) (args_L (dargs cs_R cs_L args))
      (dtabc n cs_R l)"
    using table_dtabc_cpos[OF s b sub tl] by simp
  have tr': "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R r)"
    using table_dtabc_cpos[OF s b order.refl tr] by (simp add: cpos_all)
  have "valid_mmtaux (dargs cs_R cs_L args) nt
      (update_mmtaux (dargs cs_R cs_L args) nt (dtabc n cs_R l) (dtabc n cs_R r) daux)
      (filter (\<lambda>(t, _). memR (args_ivl (dargs cs_R cs_L args)) (nt - t))
         (dauxlist3 n cs_R auxlist) @ [(nt, dtabc n cs_R l, dtabc n cs_R r)])"
    by (rule valid_update_mmtaux[OF nt tl' tr' d])
  then show ?thesis using w tl tr by (auto simp: dtaux_def dauxlist3_filter_append)
qed

lemma dtaux_result:
  assumes v: "dtaux n cs_R cs_L args cur daux auxlist"
    and s: "sorted_wrt (<) cs_R" and b: "\<forall>c \<in> set cs_R. c < n" and sub: "set cs_L \<subseteq> set cs_R"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
  shows "snd (result_mmtaux (dargs cs_R cs_L args) daux)
       = dtabc n cs_R (snd (trigger_results args cur auxlist))"
proof -
  have w: "\<forall>(t, l, r) \<in> set auxlist. table n (set cs_L) l \<and> table n (set cs_R) r"
    and d: "valid_mmtaux (dargs cs_R cs_L args) cur daux (dauxlist3 n cs_R auxlist)"
    using v by (auto simp: dtaux_def)
  have res: "result_mmtaux (dargs cs_R cs_L args) daux
      = trigger_results (dargs cs_R cs_L args) cur (dauxlist3 n cs_R auxlist)"
    by (rule valid_result_mmtaux[OF d])
  show ?thesis unfolding res by (rule dtabc_trigger_results[OF s b sub an aL aR w])
qed

(*<*)
end
(*>*)
