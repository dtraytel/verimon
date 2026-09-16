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

(*<*)
end
(*>*)
