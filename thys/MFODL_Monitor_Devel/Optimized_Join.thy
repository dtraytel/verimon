(*<*)
theory Optimized_Join
  imports "Generic_Join_Devel.Generic_Join_Correctness"
begin
(*>*)

section \<open>Optimized relational join\<close>

subsection \<open>Binary join\<close>

abbreviation "join_cond pos t \<equiv> (\<lambda>as. if pos then as \<in> t else as \<notin> t)"

abbreviation "join_filter_cond pos t \<equiv> (\<lambda>as _. join_cond pos t as)"

text \<open>The join of @{term t} over the columns @{term cs} with @{term t'} over @{term ds}, with
  shortcuts for the cases in which one table's columns are among the other's.  The last but one
  case filters the right table and brings its tuples into the join's column order
  @{term "cols_union cs ds"}.\<close>

fun bin_join :: "nat list \<Rightarrow> 'a table \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "bin_join cs t pos ds t' =
    (if t = {} then {}
    else if t' = {} then (if pos then {} else t)
    else if ds = [] then (if (pos \<longleftrightarrow> [] \<in> t') then t else {})
    else if ds = cs then (if pos then t \<inter> t' else t - t')
    else if set ds \<subseteq> set cs then {as \<in> t. join_cond pos t' (restrict ds cs as)}
    else if set cs \<subseteq> set ds \<and> pos then
      restrict (cols_union cs ds) ds ` {as \<in> t'. restrict cs ds as \<in> t}
    else join cs t pos ds t')"

lemma join_sub:
  assumes "distinct cs" "distinct ds" "table cs t" "table ds t'" "set ds \<subseteq> set cs"
  shows "join cs t pos ds t' = {as \<in> t. join_cond pos t' (restrict ds cs as)}"
proof (rule set_eqI)
  fix v
  have "cols_union cs ds = cs"
    by (rule cols_union_subset[OF assms(5)])
  then show "v \<in> join cs t pos ds t' \<longleftrightarrow> v \<in> {as \<in> t. join_cond pos t' (restrict ds cs as)}"
    using join_restrict[OF assms(1-4), of pos v] assms(5) tableD[OF assms(3), of v]
      restrict_idle[OF assms(1), of v]
    by auto
qed

lemma join_sub':
  assumes "distinct cs" "distinct ds" "table cs t" "table ds t'" "set cs \<subseteq> set ds"
  shows "join cs t True ds t' = restrict (cols_union cs ds) ds ` {as \<in> t'. restrict cs ds as \<in> t}"
    (is "_ = ?R")
proof (rule set_eqI)
  fix v
  let ?U = "cols_union cs ds"
  have U: "set ?U = set ds" "distinct ?U"
    using assms(1,2,5) by auto
  show "v \<in> join cs t True ds t' \<longleftrightarrow> v \<in> ?R"
  proof
    assume "v \<in> join cs t True ds t'"
    then have v: "wf_tuple ?U v" "restrict cs ?U v \<in> t" "restrict ds ?U v \<in> t'"
      using join_restrict[OF assms(1-4), of True v] by simp_all
    have "restrict cs ds (restrict ds ?U v) = restrict cs ?U v"
      using assms(5) by (simp add: restrict_restrict)
    moreover have "restrict ?U ds (restrict ds ?U v) = v"
      using U v(1) by (simp add: restrict_restrict restrict_idle)
    ultimately show "v \<in> ?R"
      using v(2,3) by (auto intro!: image_eqI[where x = "restrict ds ?U v"])
  next
    assume "v \<in> ?R"
    then obtain y where y: "y \<in> t'" "restrict cs ds y \<in> t" and v: "v = restrict ?U ds y"
      by blast
    have "restrict cs ?U v = restrict cs ds y"
      using U assms(5) by (simp add: v restrict_restrict)
    moreover have "restrict ds ?U v = y"
      using U y(1) tableD[OF assms(4)] by (simp add: v restrict_restrict restrict_idle assms(2))
    ultimately show "v \<in> join cs t True ds t'"
      using join_restrict[OF assms(1-4), of True v] y by (simp add: v)
  qed
qed

lemma bin_join_table:
  assumes "distinct cs" "distinct ds" "table cs t" "table ds t'"
  shows "bin_join cs t pos ds t' = join cs t pos ds t'"
proof (cases "t = {} \<or> t' = {}")
  case True
  then show ?thesis
    by (auto simp: join_def)
next
  case False
  then have ne: "t \<noteq> {}" "t' \<noteq> {}"
    by simp_all
  note sub = join_sub[OF assms]
  consider (no_cols) "ds = []"
    | (eq) "ds \<noteq> []" "ds = cs"
    | (sub) "ds \<noteq> []" "ds \<noteq> cs" "set ds \<subseteq> set cs"
    | (sub') "ds \<noteq> []" "ds \<noteq> cs" "\<not> set ds \<subseteq> set cs" "set cs \<subseteq> set ds" "pos"
    | (other) "ds \<noteq> []" "ds \<noteq> cs" "\<not> set ds \<subseteq> set cs" "\<not> (set cs \<subseteq> set ds \<and> pos)"
    by blast
  then show ?thesis
  proof cases
    case no_cols
    with assms(4) ne(2) have t': "t' = {[]}"
      by (auto simp: table_def)
    have "join cs t pos ds t' = {as \<in> t. join_cond pos t' (restrict ds cs as)}"
      by (rule sub) (simp add: no_cols)
    with ne no_cols t' show ?thesis
      by simp  next
    case eq
    with ne sub[of pos] assms(1,3) show ?thesis
      by (auto simp: restrict_idle table_def)
  next
    case sub
    with ne show ?thesis
      by (simp add: join_sub[OF assms])
  next
    case sub'
    with ne show ?thesis
      by (simp add: join_sub'[OF assms])
  next
    case other
    with ne show ?thesis
      by auto
  qed
qed

subsection \<open>Multi-way join\<close>

text \<open>The columns of the positive tables, in the order of the generic join's result.\<close>

abbreviation mcols :: "nat list list \<Rightarrow> nat list" where
  "mcols A_pos \<equiv> cols (\<Union>A\<in>set A_pos. set A)"

fun mmulti_join' :: "(nat list list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow> 'a table)" where
  "mmulti_join' A_pos A_neg L = (
    let Q = set (zip A_pos L) in
    let Q_neg = set (zip A_neg (drop (length A_pos) L)) in
    New_max_getIJ_wrapperGenericJoin Q Q_neg)"

lemma mmulti_join'_correct:
  assumes "A_pos \<noteq> []"
      and "list_all2 (\<lambda>A X. distinct A \<and> table A X) (A_pos @ A_neg) L"
      and "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set A_pos. set A)"
  shows "z \<in> mmulti_join' A_pos A_neg L \<longleftrightarrow> wf_tuple (mcols A_pos) z \<and>
    list_all2 (\<lambda>A X. restrict A (mcols A_pos) z \<in> X) A_pos (take (length A_pos) L) \<and>
    list_all2 (\<lambda>A X. restrict A (mcols A_pos) z \<notin> X) A_neg (drop (length A_pos) L)"
proof -
  define Q where "Q = set (zip A_pos L)"
  have Q_alt: "Q = set (zip A_pos (take (length A_pos) L))"
    unfolding Q_def by (fastforce simp: in_set_zip)
  define Q_neg where "Q_neg = set (zip A_neg (drop (length A_pos) L))"
  have len: "length L = length A_pos + length A_neg"
    using list_all2_lengthD[OF assms(2)] by simp
  have eq: "mmulti_join' A_pos A_neg L = New_max_getIJ_wrapperGenericJoin Q Q_neg"
    unfolding Q_def Q_neg_def by (simp del: New_max.wrapperGenericJoin.simps)
  have card: "card Q \<ge> 1"
    unfolding Q_def using assms(1) len
    by (cases A_pos; cases L) (auto simp: Suc_le_eq card_gt_0_iff)
  have wf: "\<forall>X\<in>Q \<union> Q_neg. wf_atable X"
    unfolding Q_alt Q_neg_def using assms(2)
    by (auto simp: zip_append1 list_all2_iff wf_atable_def)
  have vars: "(\<Union>(A, X)\<in>Q. set A) = (\<Union>A\<in>set A_pos. set A)"
    unfolding Q_alt using len
    by (force elim: in_set_impl_in_set_zip1[rotated, where ys="take (length A_pos) L"]
        dest: set_zip_leftD)
  have neg_vars: "\<forall>(A, X)\<in>Q_neg. set A \<subseteq> (\<Union>(A, X)\<in>Q. set A)"
    unfolding vars Q_neg_def using assms(3) by (auto dest: set_zip_leftD)
  have pos_iff: "(\<forall>(A, X)\<in>Q. P A X) \<longleftrightarrow> list_all2 P A_pos (take (length A_pos) L)" for P
    unfolding Q_alt using len by (auto simp: list_all2_iff)
  have neg_iff: "(\<forall>(A, X)\<in>Q_neg. P A X) \<longleftrightarrow> list_all2 P A_neg (drop (length A_pos) L)" for P
    unfolding Q_neg_def using len by (auto simp: list_all2_iff)
  show ?thesis
    using New_max.wrapper_correctness[OF card wf neg_vars, of z]
    unfolding eq vars pos_iff neg_iff .
qed

lemma Cons_ne_append: "xs @ y # ys \<noteq> []"
  by simp

text \<open>Merging two positive tables into their join, and a negative table into a positive one
  that covers its columns, leaves the result unchanged.\<close>

lemma list_all2_opt_True:
  assumes "list_all2 (\<lambda>A X. distinct A \<and> table A X) ((A_zs @ A_x # A_xs @ A_y # A_ys) @ A_neg)
    ((zs @ x # xs @ y # ys) @ L_neg)"
    "length A_xs = length xs" "length A_ys = length ys" "length A_zs = length zs"
  shows "list_all2 (\<lambda>A X. distinct A \<and> table A X)
    ((A_zs @ cols_union A_x A_y # A_xs @ A_ys) @ A_neg) ((zs @ join A_x x True A_y y # xs @ ys) @ L_neg)"
proof -
  have tabs: "distinct A_x" "table A_x x" "distinct A_y" "table A_y y"
    using assms by (auto simp: list_all2_append1 list_all2_append2 dest: list_all2_lengthD)
  then have "table (cols_union A_x A_y) (join A_x x True A_y y)"
    by (intro join_table) auto
  with tabs assms show ?thesis
    by (auto simp: list_all2_append list_all2_Cons1 list_all2_Cons2 dest: list_all2_lengthD)
qed

lemma mmulti_join'_opt_True:
  assumes "list_all2 (\<lambda>A X. distinct A \<and> table A X) ((A_zs @ A_x # A_xs @ A_y # A_ys) @ A_neg)
    ((zs @ x # xs @ y # ys) @ L_neg)"
    "length A_xs = length xs" "length A_ys = length ys" "length A_zs = length zs"
    "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set (A_zs @ A_x # A_xs @ A_y # A_ys). set A)"
  shows "mmulti_join' (A_zs @ A_x # A_xs @ A_y # A_ys) A_neg ((zs @ x # xs @ y # ys) @ L_neg) =
    mmulti_join' (A_zs @ cols_union A_x A_y # A_xs @ A_ys) A_neg
    ((zs @ join A_x x True A_y y # xs @ ys) @ L_neg)"
proof -
  let ?A = "A_zs @ A_x # A_xs @ A_y # A_ys" and ?A' = "A_zs @ cols_union A_x A_y # A_xs @ A_ys"
  let ?L = "zs @ x # xs @ y # ys" and ?L' = "zs @ join A_x x True A_y y # xs @ ys"
  have tabs: "distinct A_x" "table A_x x" "distinct A_y" "table A_y y"
    using assms(1-4) by (auto simp: list_all2_append1 list_all2_append2 dest: list_all2_lengthD)
  have W: "(\<Union>A\<in>set ?A'. set A) = (\<Union>A\<in>set ?A. set A)"
    by auto
  have take_drop: "take (length ?A) (?L @ L_neg) = ?L" "drop (length ?A) (?L @ L_neg) = L_neg"
    "take (length ?A') (?L' @ L_neg) = ?L'" "drop (length ?A') (?L' @ L_neg) = L_neg"
    using assms(2-4) by simp_all
  have res: "restrict (cols_union A_x A_y) W z \<in> join A_x x True A_y y \<longleftrightarrow>
    restrict A_x W z \<in> x \<and> restrict A_y W z \<in> y" for W z
  proof -
    have sub: "set A_x \<subseteq> set (cols_union A_x A_y)" "set A_y \<subseteq> set (cols_union A_x A_y)"
      by auto
    show ?thesis
      using join_restrict[OF tabs(1,3,2,4), of True "restrict (cols_union A_x A_y) W z"]
      by (simp add: restrict_restrict[OF sub(1)] restrict_restrict[OF sub(2)])
  qed
  show ?thesis
  proof (rule set_eqI)
    fix z
    show "z \<in> mmulti_join' ?A A_neg (?L @ L_neg) \<longleftrightarrow> z \<in> mmulti_join' ?A' A_neg (?L' @ L_neg)"
      unfolding mmulti_join'_correct[OF Cons_ne_append assms(1,5)]
        mmulti_join'_correct[OF Cons_ne_append list_all2_opt_True[OF assms(1-4)] assms(5)[folded W]]
        W take_drop
      using assms(2-4) by (auto simp: list_all2_append res simp del: mmulti_join'.simps)
  qed
qed

lemma list_all2_opt_False:
  assumes "list_all2 (\<lambda>A X. distinct A \<and> table A X)
    ((A_zs @ A_x # A_xs) @ (A_ws @ A_y # A_ys)) ((zs @ x # xs) @ (ws @ y # ys))"
    "length A_ws = length ws" "length A_xs = length xs"
    "length A_ys = length ys" "length A_zs = length zs"
    "set A_y \<subseteq> set A_x"
  shows "list_all2 (\<lambda>A X. distinct A \<and> table A X)
    ((A_zs @ A_x # A_xs) @ (A_ws @ A_ys)) ((zs @ join A_x x False A_y y # xs) @ (ws @ ys))"
proof -
  have tabs: "distinct A_x" "table A_x x" "distinct A_y" "table A_y y"
    using assms by (auto simp: list_all2_append1 list_all2_append2 dest: list_all2_lengthD)
  then have "table A_x (join A_x x False A_y y)"
    using assms(6) by (intro join_table) (auto simp: cols_union_subset)
  with tabs assms show ?thesis
    by (auto simp: list_all2_append list_all2_Cons1 list_all2_Cons2 dest: list_all2_lengthD)
qed

lemma mmulti_join'_opt_False:
  assumes "list_all2 (\<lambda>A X. distinct A \<and> table A X)
    ((A_zs @ A_x # A_xs) @ (A_ws @ A_y # A_ys)) ((zs @ x # xs) @ (ws @ y # ys))"
    "length A_ws = length ws" "length A_xs = length xs"
    "length A_ys = length ys" "length A_zs = length zs"
    "set A_y \<subseteq> set A_x"
    "(\<Union>A\<in>set (A_ws @ A_y # A_ys). set A) \<subseteq> (\<Union>A\<in>set (A_zs @ A_x # A_xs). set A)"
  shows "mmulti_join' (A_zs @ A_x # A_xs) (A_ws @ A_y # A_ys) ((zs @ x # xs) @ (ws @ y # ys)) =
    mmulti_join' (A_zs @ A_x # A_xs) (A_ws @ A_ys) ((zs @ join A_x x False A_y y # xs) @ (ws @ ys))"
proof -
  let ?A = "A_zs @ A_x # A_xs" and ?L = "zs @ x # xs" and ?L' = "zs @ join A_x x False A_y y # xs"
  have tabs: "distinct A_x" "table A_x x" "distinct A_y" "table A_y y"
    using assms(1-5) by (auto simp: list_all2_append1 list_all2_append2 dest: list_all2_lengthD)
  have take_drop: "take (length ?A) (?L @ ws @ y # ys) = ?L" "drop (length ?A) (?L @ ws @ y # ys) = ws @ y # ys"
    "take (length ?A) (?L' @ ws @ ys) = ?L'" "drop (length ?A) (?L' @ ws @ ys) = ws @ ys"
    using assms(3,5) by simp_all
  have neg: "(\<Union>A\<in>set (A_ws @ A_ys). set A) \<subseteq> (\<Union>A\<in>set ?A. set A)"
    using assms(7) by auto
  have res: "restrict A_x W z \<in> join A_x x False A_y y \<longleftrightarrow>
    restrict A_x W z \<in> x \<and> restrict A_y W z \<notin> y" for W z
    using join_sub[OF tabs(1,3,2,4) assms(6), of False] assms(6)
    by (simp add: restrict_restrict)
  show ?thesis
  proof (rule set_eqI)
    fix z
    show "z \<in> mmulti_join' ?A (A_ws @ A_y # A_ys) (?L @ ws @ y # ys) \<longleftrightarrow>
      z \<in> mmulti_join' ?A (A_ws @ A_ys) (?L' @ ws @ ys)"
      unfolding mmulti_join'_correct[OF Cons_ne_append assms(1) assms(7)]
        mmulti_join'_correct[OF Cons_ne_append list_all2_opt_False[OF assms(1-6)] neg]
        take_drop
      using assms(2-5) by (auto simp: list_all2_append res simp del: mmulti_join'.simps)
  qed
qed

fun find_sub_in :: "'a list \<Rightarrow> 'a list list \<Rightarrow> bool \<Rightarrow>
  ('a list list \<times> 'a list \<times> 'a list list) option" where
  "find_sub_in X [] b = None"
| "find_sub_in X (x # xs) b = (if (set x \<subseteq> set X \<or> (b \<and> set X \<subseteq> set x)) then Some ([], x, xs)
    else (case find_sub_in X xs b of None \<Rightarrow> None | Some (ys, z, zs) \<Rightarrow> Some (x # ys, z, zs)))"

lemma find_sub_in_sound: "find_sub_in X xs b = Some (ys, z, zs) \<Longrightarrow>
  xs = ys @ z # zs \<and> (set z \<subseteq> set X \<or> (b \<and> set X \<subseteq> set z))"
  by (induction X xs b arbitrary: ys z zs rule: find_sub_in.induct)
     (fastforce split: if_splits option.splits)+

fun find_sub_True :: "'a list list \<Rightarrow>
  ('a list list \<times> 'a list \<times> 'a list list \<times> 'a list \<times> 'a list list) option" where
  "find_sub_True [] = None"
| "find_sub_True (x # xs) = (case find_sub_in x xs True of None \<Rightarrow>
    (case find_sub_True xs of None \<Rightarrow> None
    | Some (ys, w, ws, z, zs) \<Rightarrow> Some (x # ys, w, ws, z, zs))
  | Some (ys, z, zs) \<Rightarrow> Some ([], x, ys, z, zs))"

lemma find_sub_True_sound: "find_sub_True xs = Some (ys, w, ws, z, zs) \<Longrightarrow>
  xs = ys @ w # ws @ z # zs \<and> (set z \<subseteq> set w \<or> set w \<subseteq> set z)"
  using find_sub_in_sound
  by (induction xs arbitrary: ys w ws z zs rule: find_sub_True.induct)
     (fastforce split: option.splits)+

fun find_sub_False :: "'a list list \<Rightarrow> 'a list list \<Rightarrow>
  (('a list list \<times> 'a list \<times> 'a list list) \<times> ('a list list \<times> 'a list \<times> 'a list list)) option" where
  "find_sub_False [] ns = None"
| "find_sub_False (x # xs) ns = (case find_sub_in x ns False of None \<Rightarrow>
    (case find_sub_False xs ns of None \<Rightarrow> None
    | Some ((rs, w, ws), (ys, z, zs)) \<Rightarrow> Some ((x # rs, w, ws), (ys, z, zs)))
  | Some (ys, z, zs) \<Rightarrow> Some (([], x, xs), (ys, z, zs)))"

lemma find_sub_False_sound: "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs)) \<Longrightarrow>
  xs = rs @ w # ws \<and> ns = ys @ z # zs \<and> (set z \<subseteq> set w)"
  using find_sub_in_sound
  by (induction xs ns arbitrary: rs w ws ys z zs rule: find_sub_False.induct)
     (fastforce split: option.splits)+
fun proj_list_3 :: "'a list \<Rightarrow> ('b list \<times> 'b \<times> 'b list) \<Rightarrow> ('a list \<times> 'a \<times> 'a list)" where
  "proj_list_3 xs (ys, z, zs) = (take (length ys) xs, xs ! (length ys),
    take (length zs) (drop (length ys + 1) xs))"

lemma proj_list_3_same:
  assumes "proj_list_3 xs (ys, z, zs) = (ys', z', zs')"
    "length xs = length ys + 1 + length zs"
  shows "xs = ys' @ z' # zs'"
  using assms by (auto simp add: id_take_nth_drop)

lemma proj_list_3_length:
  assumes "proj_list_3 xs (ys, z, zs) = (ys', z', zs')"
    "length xs = length ys + 1 + length zs"
  shows "length ys = length ys'" "length zs = length zs'"
  using assms by auto

fun proj_list_5 :: "'a list \<Rightarrow>
  ('b list \<times> 'b \<times> 'b list \<times> 'b \<times> 'b list) \<Rightarrow>
  ('a list \<times> 'a \<times> 'a list \<times> 'a \<times> 'a list)" where
  "proj_list_5 xs (ys, w, ws, z, zs) = (take (length ys) xs, xs ! (length ys),
    take (length ws) (drop (length ys + 1) xs), xs ! (length ys + 1 + length ws),
    drop (length ys + 1 + length ws + 1) xs)"

lemma proj_list_5_same:
  assumes "proj_list_5 xs (ys, w, ws, z, zs) = (ys', w', ws', z', zs')"
    "length xs = length ys + 1 + length ws + 1 + length zs"
  shows "xs = ys' @ w' # ws' @ z' # zs'"
proof -
  have "xs ! length ys # take (length ws) (drop (Suc (length ys)) xs) = take (Suc (length ws)) (drop (length ys) xs)"
    using assms(2) by (simp add: list_eq_iff_nth_eq nth_Cons split: nat.split)
  moreover have "take (Suc (length ws)) (drop (length ys) xs) @ drop (Suc (length ys + length ws)) xs =
      drop (length ys) xs"
    unfolding Suc_eq_plus1 add.assoc[of _ _ 1] add.commute[of _ "length ws + 1"]
      drop_drop[symmetric, of "length ws + 1"] append_take_drop_id ..
  ultimately show ?thesis
    using assms by (auto simp: Cons_nth_drop_Suc append_Cons[symmetric])
qed

lemma proj_list_5_length:
  assumes "proj_list_5 xs (ys, w, ws, z, zs) = (ys', w', ws', z', zs')"
    "length xs = length ys + 1 + length ws + 1 + length zs"
  shows "length ys = length ys'" "length ws = length ws'"
    "length zs = length zs'"
  using assms by auto

fun dominate_True :: "nat list list \<Rightarrow> 'a table list \<Rightarrow>
  ((nat list list \<times> nat list \<times> nat list list \<times> nat list \<times> nat list list) \<times>
  ('a table list \<times> 'a table \<times> 'a table list \<times> 'a table \<times> 'a table list)) option" where  "dominate_True A_pos L_pos = (case find_sub_True A_pos of None \<Rightarrow> None
  | Some split \<Rightarrow> Some (split, proj_list_5 L_pos split))"

lemma find_sub_True_proj_list_5_same:
  assumes "find_sub_True xs = Some (ys, w, ws, z, zs)" "length xs = length xs'"
    "proj_list_5 xs' (ys, w, ws, z, zs) = (ys', w', ws', z', zs')"
  shows "xs' = ys' @ w' # ws' @ z' # zs'"
proof -
  have len: "length xs' = length ys + 1 + length ws + 1 + length zs"
    using find_sub_True_sound[OF assms(1)] by (auto simp add: assms(2)[symmetric])
  show ?thesis
    using proj_list_5_same[OF assms(3) len] .
qed

lemma find_sub_True_proj_list_5_length:
  assumes "find_sub_True xs = Some (ys, w, ws, z, zs)" "length xs = length xs'"
    "proj_list_5 xs' (ys, w, ws, z, zs) = (ys', w', ws', z', zs')"
  shows "length ys = length ys'" "length ws = length ws'"
    "length zs = length zs'"
  using find_sub_True_sound[OF assms(1)] proj_list_5_length[OF assms(3)] assms(2) by auto

lemma dominate_True_sound:
  assumes "dominate_True A_pos L_pos = Some ((A_zs, A_x, A_xs, A_y, A_ys), (zs, x, xs, y, ys))"
    "length A_pos = length L_pos"
  shows "A_pos = A_zs @ A_x # A_xs @ A_y # A_ys" "L_pos = zs @ x # xs @ y # ys"
    "length A_xs = length xs" "length A_ys = length ys" "length A_zs = length zs"
proof -
  have find: "find_sub_True A_pos = Some (A_zs, A_x, A_xs, A_y, A_ys)"
    and proj: "proj_list_5 L_pos (A_zs, A_x, A_xs, A_y, A_ys) = (zs, x, xs, y, ys)"
    using assms(1) by (auto simp del: proj_list_5.simps split: option.splits)
  show "A_pos = A_zs @ A_x # A_xs @ A_y # A_ys"
    using find_sub_True_sound[OF find] by simp
  show "L_pos = zs @ x # xs @ y # ys"
    using find_sub_True_proj_list_5_same[OF find assms(2) proj] .
  show "length A_zs = length zs" "length A_xs = length xs" "length A_ys = length ys"
    using find_sub_True_proj_list_5_length[OF find assms(2) proj] .
qed

fun dominate_False :: "nat list list \<Rightarrow> 'a table list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow>
  (((nat list list \<times> nat list \<times> nat list list) \<times> nat list list \<times> nat list \<times> nat list list) \<times>
  (('a table list \<times> 'a table \<times> 'a table list) \<times>
  'a table list \<times> 'a table \<times> 'a table list)) option" where
  "dominate_False A_pos L_pos A_neg L_neg = (case find_sub_False A_pos A_neg of None \<Rightarrow> None
  | Some (pos_split, neg_split) \<Rightarrow>
    Some ((pos_split, neg_split), (proj_list_3 L_pos pos_split, proj_list_3 L_neg neg_split)))"

lemma find_sub_False_proj_list_3_same_left:
  assumes "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs))"
    "length xs = length xs'" "proj_list_3 xs' (rs, w, ws) = (rs', w', ws')"
  shows "xs' = rs' @ w' # ws'"
proof -
  have len: "length xs' = length rs + 1 + length ws"
    using find_sub_False_sound[OF assms(1)] by (auto simp add: assms(2)[symmetric])
  show ?thesis
    using proj_list_3_same[OF assms(3) len] .
qed

lemma find_sub_False_proj_list_3_length_left:
  assumes "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs))"
    "length xs = length xs'" "proj_list_3 xs' (rs, w, ws) = (rs', w', ws')"
  shows "length rs = length rs'" "length ws = length ws'"
  using find_sub_False_sound[OF assms(1)] proj_list_3_length[OF assms(3)] assms(2) by auto

lemma find_sub_False_proj_list_3_same_right:
  assumes "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs))"
    "length ns = length ns'" "proj_list_3 ns' (ys, z, zs) = (ys', z', zs')"
  shows "ns' = ys' @ z' # zs'"
proof -
  have len: "length ns' = length ys + 1 + length zs"
    using find_sub_False_sound[OF assms(1)] by (auto simp add: assms(2)[symmetric])
  show ?thesis
    using proj_list_3_same[OF assms(3) len] .
qed

lemma find_sub_False_proj_list_3_length_right:
  assumes "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs))"
    "length ns = length ns'" "proj_list_3 ns' (ys, z, zs) = (ys', z', zs')"
  shows "length ys = length ys'" "length zs = length zs'"
  using find_sub_False_sound[OF assms(1)] proj_list_3_length[OF assms(3)] assms(2) by auto

lemma dominate_False_sound:
  assumes "dominate_False A_pos L_pos A_neg L_neg =
    Some (((A_zs, A_x, A_xs), A_ws, A_y, A_ys), ((zs, x, xs), ws, y, ys))"
    "length A_pos = length L_pos" "length A_neg = length L_neg"
  shows "A_pos = (A_zs @ A_x # A_xs)" "A_neg = A_ws @ A_y # A_ys"
    "L_pos = (zs @ x # xs)" "L_neg = ws @ y # ys"
    "length A_ws = length ws" "length A_xs = length xs"
    "length A_ys = length ys" "length A_zs = length zs"
    "set A_y \<subseteq> set A_x"
proof -
  have find: "find_sub_False A_pos A_neg = Some ((A_zs, A_x, A_xs), (A_ws, A_y, A_ys))"
    and proj: "proj_list_3 L_pos (A_zs, A_x, A_xs) = (zs, x, xs)"
      "proj_list_3 L_neg (A_ws, A_y, A_ys) = (ws, y, ys)"
    using assms(1) by (auto simp del: proj_list_3.simps split: option.splits)
  show "A_pos = A_zs @ A_x # A_xs" "A_neg = A_ws @ A_y # A_ys" "set A_y \<subseteq> set A_x"
    using find_sub_False_sound[OF find] by simp_all
  show "L_pos = zs @ x # xs"
    using find_sub_False_proj_list_3_same_left[OF find assms(2) proj(1)] .
  show "L_neg = ws @ y # ys"
    using find_sub_False_proj_list_3_same_right[OF find assms(3) proj(2)] .
  show "length A_zs = length zs" "length A_xs = length xs"
    using find_sub_False_proj_list_3_length_left[OF find assms(2) proj(1)] .
  show "length A_ws = length ws" "length A_ys = length ys"
    using find_sub_False_proj_list_3_length_right[OF find assms(3) proj(2)] .
qed

function mmulti_join_gen :: "(nat list list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow> 'a table)" where
  "mmulti_join_gen A_pos A_neg L = (if length A_pos + length A_neg \<noteq> length L then {} else
    let L_pos = take (length A_pos) L; L_neg = drop (length A_pos) L in
    (case dominate_True A_pos L_pos of None \<Rightarrow>
      (case dominate_False A_pos L_pos A_neg L_neg of None \<Rightarrow> mmulti_join' A_pos A_neg L
      | Some (((A_zs, A_x, A_xs), A_ws, A_y, A_ys), ((zs, x, xs), ws, y, ys)) \<Rightarrow>
        mmulti_join_gen (A_zs @ A_x # A_xs) (A_ws @ A_ys)
        ((zs @ bin_join A_x x False A_y y # xs) @ (ws @ ys)))
    | Some ((A_zs, A_x, A_xs, A_y, A_ys), (zs, x, xs, y, ys)) \<Rightarrow>
      mmulti_join_gen (A_zs @ cols_union A_x A_y # A_xs @ A_ys) A_neg
      ((zs @ bin_join A_x x True A_y y # xs @ ys) @ L_neg)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(A_pos, A_neg, L). length A_pos + length A_neg)")
    (use find_sub_True_sound find_sub_False_sound in \<open>fastforce split: option.splits\<close>)+

lemma mmulti_join_gen_link:
  assumes "A_pos \<noteq> []"
      and "list_all2 (\<lambda>A X. distinct A \<and> table A X) (A_pos @ A_neg) L"
      and "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set A_pos. set A)"
    shows "mmulti_join_gen A_pos A_neg L = mmulti_join' A_pos A_neg L"
  using assms
proof (induction A_pos A_neg L rule: mmulti_join_gen.induct)
  case (1 A_pos A_neg L)
  define L_pos where "L_pos = take (length A_pos) L"
  define L_neg where "L_neg = drop (length A_pos) L"
  have L_def: "L = L_pos @ L_neg"
    using L_pos_def L_neg_def by auto
  have lens_match: "length A_pos = length L_pos" "length A_neg = length L_neg"
    using L_pos_def L_neg_def 1(4)[unfolded L_def] by (auto dest: list_all2_lengthD)
  then have lens_sum: "length A_pos + length A_neg = length L"
    by (auto simp add: L_def)
  show ?case
  proof (cases "dominate_True A_pos L_pos")
    case None
    note dom_True = None
    show ?thesis
    proof (cases "dominate_False A_pos L_pos A_neg L_neg")
      case None
      show ?thesis
        by (subst mmulti_join_gen.simps)
           (simp del: dominate_True.simps dominate_False.simps mmulti_join_gen.simps
            mmulti_join'.simps add: Let_def dom_True L_pos_def[symmetric] None
            L_neg_def[symmetric] lens_sum split: option.splits)
    next
      case (Some a)
      then obtain A_zs A_x A_xs A_ws A_y A_ys zs x xs ws y ys where
        dom_False: "dominate_False A_pos L_pos A_neg L_neg =
        Some (((A_zs, A_x, A_xs), A_ws, A_y, A_ys), ((zs, x, xs), ws, y, ys))"
        by (cases a) auto
      note sound = dominate_False_sound[OF dom_False lens_match]
      note list_all2 = 1(4)[unfolded L_def sound(1-4)]
      have lens: "length A_ws = length ws" "length A_xs = length xs"
        "length A_ys = length ys" "length A_zs = length zs"
        using sound by auto
      have sub: "set A_y \<subseteq> set A_x"
        using sound by auto
      have neg: "(\<Union>A\<in>set (A_ws @ A_y # A_ys). set A) \<subseteq> (\<Union>A\<in>set (A_zs @ A_x # A_xs). set A)"
        using 1(5) unfolding sound(1,2) .
      have neg': "(\<Union>A\<in>set (A_ws @ A_ys). set A) \<subseteq> (\<Union>A\<in>set (A_zs @ A_x # A_xs). set A)"
        using neg by auto
      have list_all2': "list_all2 (\<lambda>A X. distinct A \<and> table A X)
        ((A_zs @ A_x # A_xs) @ (A_ws @ A_ys)) ((zs @ join A_x x False A_y y # xs) @ (ws @ ys))"
        using list_all2_opt_False[OF list_all2 lens sub] .
      have tabs: "distinct A_x" "table A_x x" "distinct A_y" "table A_y y"
        using list_all2 by (auto simp add: lens list_all2_append)
      have bin_join_conv: "join A_x x False A_y y = bin_join A_x x False A_y y"
        using bin_join_table[OF tabs(1,3,2,4), symmetric] .
      have mmulti: "mmulti_join_gen A_pos A_neg L = mmulti_join_gen (A_zs @ A_x # A_xs) (A_ws @ A_ys)
        ((zs @ bin_join A_x x False A_y y # xs) @ (ws @ ys))"
        by (subst mmulti_join_gen.simps)
           (simp del: dominate_True.simps dominate_False.simps mmulti_join_gen.simps
            add: Let_def dom_True L_pos_def[symmetric] L_neg_def[symmetric] dom_False lens_sum)
      show ?thesis
        unfolding mmulti
        unfolding L_def sound(1-4)
        by (rule 1(1)[OF _ L_pos_def L_neg_def dom_True dom_False,
            OF _ _ _ _ _ _ _ _ _ _ _ _ _ list_all2'[unfolded bin_join_conv] neg',
            unfolded mmulti_join'_opt_False[OF list_all2 lens sub neg, symmetric,
            unfolded bin_join_conv]])
           (auto simp add: lens_sum)
    qed
  next
    case (Some a)
    then obtain A_zs A_x A_xs A_y A_ys zs x xs y ys where dom_True: "dominate_True A_pos L_pos =
      Some ((A_zs, A_x, A_xs, A_y, A_ys), (zs, x, xs, y, ys))"
      by (cases a) auto
    note sound = dominate_True_sound[OF dom_True lens_match(1)]
    note list_all2 = 1(4)[unfolded L_def sound(1,2)]
    have lens: "length A_xs = length xs" "length A_ys = length ys" "length A_zs = length zs"
      using sound by auto
    have neg: "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set (A_zs @ A_x # A_xs @ A_y # A_ys). set A)"
      using 1(5) unfolding sound(1) .
    have neg': "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set (A_zs @ cols_union A_x A_y # A_xs @ A_ys). set A)"
      using neg by auto
    have list_all2': "list_all2 (\<lambda>A X. distinct A \<and> table A X)
      ((A_zs @ cols_union A_x A_y # A_xs @ A_ys) @ A_neg) ((zs @ join A_x x True A_y y # xs @ ys) @ L_neg)"
      using list_all2_opt_True[OF list_all2 lens] .
    have tabs: "distinct A_x" "table A_x x" "distinct A_y" "table A_y y"
        using list_all2 by (auto simp add: lens list_all2_append)
    have bin_join_conv: "join A_x x True A_y y = bin_join A_x x True A_y y"
      using bin_join_table[OF tabs(1,3,2,4), symmetric] .
    have mmulti: "mmulti_join_gen A_pos A_neg L = mmulti_join_gen (A_zs @ cols_union A_x A_y # A_xs @ A_ys)
      A_neg ((zs @ bin_join A_x x True A_y y # xs @ ys) @ L_neg)"
      by (subst mmulti_join_gen.simps)
         (simp del: dominate_True.simps dominate_False.simps mmulti_join_gen.simps
          add: Let_def dom_True L_pos_def[symmetric] L_neg_def lens_sum)
    show ?thesis
      unfolding mmulti
      unfolding L_def sound(1,2)
      by (rule 1(2)[OF _ L_pos_def L_neg_def dom_True,
          OF _ _ _ _ _ _ _ _ _ _ _ list_all2'[unfolded bin_join_conv] neg',
          unfolded mmulti_join'_opt_True[OF list_all2 lens neg, symmetric,
          unfolded bin_join_conv]])
         (auto simp add: lens_sum)
  qed
qed

lemma mmulti_join_gen_correct:
  assumes "A_pos \<noteq> []"
      and "list_all2 (\<lambda>A X. distinct A \<and> table A X) (A_pos @ A_neg) L"
      and "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set A_pos. set A)"
  shows "z \<in> mmulti_join_gen A_pos A_neg L \<longleftrightarrow> wf_tuple (mcols A_pos) z \<and>
    list_all2 (\<lambda>A X. restrict A (mcols A_pos) z \<in> X) A_pos (take (length A_pos) L) \<and>
    list_all2 (\<lambda>A X. restrict A (mcols A_pos) z \<notin> X) A_neg (drop (length A_pos) L)"
  unfolding mmulti_join_gen_link[OF assms] using mmulti_join'_correct[OF assms] .

subsection \<open>Multi-way join as a sequence of binary joins\<close>

text \<open>
  The worst-case optimal generic join above has large constant factors in the generated code.
  The monitor therefore evaluates multi-way joins as a left-deep sequence of binary joins
  (which use an index on the common columns, see @{const bin_join}) followed by anti-joins
  for the negated conjuncts. The correctness statement @{text mmulti_join_correct} is the same
  as for the generic join. The two strategies produce their results in different column
  orders (the generic join sorts the columns, the binary joins accumulate them with
  @{const cols_union}); @{text mmulti_join} takes the column order of its result as an
  argument and reorders the tuples if needed.
\<close>

lemma restrict_mem_join:
  assumes "distinct cs" "distinct ds" "table cs X" "table ds Y" "\<not> b \<Longrightarrow> set ds \<subseteq> set cs"
  shows "restrict (cols_union cs ds) W z \<in> join cs X b ds Y \<longleftrightarrow>
    restrict cs W z \<in> X \<and> (if b then restrict ds W z \<in> Y else restrict ds W z \<notin> Y)"
proof -
  have "restrict (cols_union cs ds) W z \<in> join cs X b ds Y \<longleftrightarrow>
    wf_tuple (cols_union cs ds) (restrict (cols_union cs ds) W z) \<and>
    restrict cs (cols_union cs ds) (restrict (cols_union cs ds) W z) \<in> X \<and>
    (if b then restrict ds (cols_union cs ds) (restrict (cols_union cs ds) W z) \<in> Y
     else restrict ds (cols_union cs ds) (restrict (cols_union cs ds) W z) \<notin> Y)"
    by (rule join_restrict[OF assms])
  then show ?thesis
    by (cases b) (simp_all add: restrict_restrict)
qed

fun mmulti_join_pos :: "nat list \<Rightarrow> 'a table \<Rightarrow> (nat list \<times> 'a table) list \<Rightarrow> nat list \<times> 'a table" where
  "mmulti_join_pos cs t [] = (cs, t)"
| "mmulti_join_pos cs t ((cs', t') # L) = mmulti_join_pos (cols_union cs cs') (bin_join cs t True cs' t') L"

fun mmulti_join_neg :: "nat list \<Rightarrow> 'a table \<Rightarrow> (nat list \<times> 'a table) list \<Rightarrow> 'a table" where
  "mmulti_join_neg cs t [] = t"
| "mmulti_join_neg cs t ((cs', t') # L) = mmulti_join_neg cs (bin_join cs t False cs' t') L"

text \<open>
  The choice between the two evaluation strategies is left open in the formalization: the
  constant @{text use_generic_join} is unspecified, and the correctness of @{text mmulti_join}
  below is proved for both of its values. The generated code reads it from a mutable flag
  (see theory @{text Code_Opt}), which the front end sets from the command line option
  @{text "-generic_join"}.
\<close>

consts use_generic_join :: bool

fun mmulti_join_pw :: "nat list list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow> nat list \<times> 'a table" where
  "mmulti_join_pw A_pos A_neg L = (case zip A_pos L of [] \<Rightarrow> ([], {})
    | (A, t) # Lpos \<Rightarrow> (case mmulti_join_pos A t Lpos of (A', t') \<Rightarrow>
        (A', mmulti_join_neg A' t' (zip A_neg (drop (length A_pos) L)))))"

definition reorder :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "reorder cs ds t = (if cs = ds then t else restrict cs ds ` t)"

fun mmulti_join :: "nat list \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow> 'a table" where
  "mmulti_join cs A_pos A_neg L =
    (if use_generic_join then reorder cs (mcols A_pos) (mmulti_join_gen A_pos A_neg L)
    else (case mmulti_join_pw A_pos A_neg L of (cs', t) \<Rightarrow> reorder cs cs' t))"

lemma mem_reorder:
  assumes "distinct cs" "distinct ds" "set cs = set ds" "table ds t"
  shows "z \<in> reorder cs ds t \<longleftrightarrow> wf_tuple cs z \<and> restrict ds cs z \<in> t"
proof (cases "cs = ds")
  case True
  then show ?thesis
    using assms(1,4) by (auto simp: reorder_def restrict_idle dest: tableD)
next
  case False
  show ?thesis
  proof
    assume "z \<in> reorder cs ds t"
    then obtain y where "y \<in> t" "z = restrict cs ds y"
      using False by (auto simp: reorder_def)
    moreover have "restrict ds cs (restrict cs ds y) = y" if "y \<in> t" for y
      using assms that by (simp add: restrict_restrict restrict_idle tableD)
    ultimately show "wf_tuple cs z \<and> restrict ds cs z \<in> t"
      by simp
  next
    assume z: "wf_tuple cs z \<and> restrict ds cs z \<in> t"
    then have "restrict cs ds (restrict ds cs z) = z"
      using assms(1,3) by (simp add: restrict_restrict restrict_idle)
    with z False show "z \<in> reorder cs ds t"
      by (auto simp: reorder_def intro: rev_image_eqI)
  qed
qed

lemma mmulti_join_pos_correct:
  assumes "distinct cs" "table cs t" "\<forall>B X. (B, X) \<in> set L \<longrightarrow> distinct B \<and> table B X"
  shows "distinct (fst (mmulti_join_pos cs t L)) \<and>
    set (fst (mmulti_join_pos cs t L)) = set cs \<union> (\<Union>BX \<in> set L. set (fst BX)) \<and>
    table (fst (mmulti_join_pos cs t L)) (snd (mmulti_join_pos cs t L)) \<and>
    (\<forall>z. z \<in> snd (mmulti_join_pos cs t L) \<longleftrightarrow> wf_tuple (fst (mmulti_join_pos cs t L)) z \<and>
       restrict cs (fst (mmulti_join_pos cs t L)) z \<in> t \<and>
       (\<forall>B X. (B, X) \<in> set L \<longrightarrow> restrict B (fst (mmulti_join_pos cs t L)) z \<in> X))"
  using assms
proof (induction L arbitrary: cs t)
  case Nil
  then show ?case
    by (auto simp: restrict_idle dest: tableD)
next
  case (Cons Bu L)
  obtain B u where Bu: "Bu = (B, u)"
    by (cases Bu)
  have tab': "distinct B" "table B u"
    using Cons.prems(3) by (auto simp: Bu)
  have join: "bin_join cs t True B u = join cs t True B u"
    by (rule bin_join_table[OF Cons.prems(1) tab'(1) Cons.prems(2) tab'(2)])
  have tab_join: "table (cols_union cs B) (join cs t True B u)"
    by (rule join_table[OF Cons.prems(2) tab'(2)]) auto
  have eq: "mmulti_join_pos cs t (Bu # L) = mmulti_join_pos (cols_union cs B) (join cs t True B u) L"
    by (simp only: Bu mmulti_join_pos.simps join)
  have IH: "distinct (fst (mmulti_join_pos (cols_union cs B) (join cs t True B u) L)) \<and>
    set (fst (mmulti_join_pos (cols_union cs B) (join cs t True B u) L)) =
      set (cols_union cs B) \<union> (\<Union>BX \<in> set L. set (fst BX)) \<and>
    table (fst (mmulti_join_pos (cols_union cs B) (join cs t True B u) L))
      (snd (mmulti_join_pos (cols_union cs B) (join cs t True B u) L)) \<and>
    (\<forall>z. z \<in> snd (mmulti_join_pos (cols_union cs B) (join cs t True B u) L) \<longleftrightarrow>
      wf_tuple (fst (mmulti_join_pos (cols_union cs B) (join cs t True B u) L)) z \<and>
      restrict (cols_union cs B) (fst (mmulti_join_pos (cols_union cs B) (join cs t True B u) L)) z
        \<in> join cs t True B u \<and>
      (\<forall>B' X. (B', X) \<in> set L \<longrightarrow>
        restrict B' (fst (mmulti_join_pos (cols_union cs B) (join cs t True B u) L)) z \<in> X))"
    using Cons.prems(1,3) tab' tab_join by (intro Cons.IH) (auto simp: Bu)
  show ?case
    unfolding eq
    using IH restrict_mem_join[OF Cons.prems(1) tab'(1) Cons.prems(2) tab'(2), of True]
    by (auto simp: Bu)
qed

lemma mmulti_join_neg_correct:
  assumes "distinct cs" "table cs t" "\<forall>B X. (B, X) \<in> set L \<longrightarrow> distinct B \<and> table B X \<and> set B \<subseteq> set cs"
  shows "table cs (mmulti_join_neg cs t L) \<and>
    (\<forall>z. z \<in> mmulti_join_neg cs t L \<longleftrightarrow> z \<in> t \<and> (\<forall>B X. (B, X) \<in> set L \<longrightarrow> restrict B cs z \<notin> X))"
  using assms
proof (induction L arbitrary: t)
  case Nil
  then show ?case
    by simp
next
  case (Cons Bu L)
  obtain B u where Bu: "Bu = (B, u)"
    by (cases Bu)
  have tab': "distinct B" "table B u" and sub: "set B \<subseteq> set cs"
    using Cons.prems(3) by (auto simp: Bu)
  have join: "bin_join cs t False B u = join cs t False B u"
    by (rule bin_join_table[OF Cons.prems(1) tab'(1) Cons.prems(2) tab'(2)])
  have tab_join: "table cs (join cs t False B u)"
    by (rule join_table[OF Cons.prems(2) tab'(2)]) (use sub in \<open>auto simp: cols_union_subset\<close>)
  have *: "join cs t False B u = {as \<in> t. restrict B cs as \<notin> u}"
    using join_sub[OF Cons.prems(1) tab'(1) Cons.prems(2) tab'(2) sub, of False] by simp
  have eq: "mmulti_join_neg cs t (Bu # L) = mmulti_join_neg cs (join cs t False B u) L"
    by (simp only: Bu mmulti_join_neg.simps join)
  have prem: "\<forall>B X. (B, X) \<in> set L \<longrightarrow> distinct B \<and> table B X \<and> set B \<subseteq> set cs"
    using Cons.prems(3) by auto
  show ?case
    unfolding eq
    using Cons.IH[OF Cons.prems(1) tab_join prem] Cons.prems(3) * by (auto simp: Bu)
qed

lemma mmulti_join_pw_correct:
  assumes "A_pos \<noteq> []"
      and "list_all2 (\<lambda>A X. distinct A \<and> table A X) (A_pos @ A_neg) L"
      and "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set A_pos. set A)"
  shows "distinct (fst (mmulti_join_pw A_pos A_neg L)) \<and>
    set (fst (mmulti_join_pw A_pos A_neg L)) = (\<Union>A\<in>set A_pos. set A) \<and>
    table (fst (mmulti_join_pw A_pos A_neg L)) (snd (mmulti_join_pw A_pos A_neg L)) \<and>
    (\<forall>z. z \<in> snd (mmulti_join_pw A_pos A_neg L) \<longleftrightarrow> wf_tuple (fst (mmulti_join_pw A_pos A_neg L)) z \<and>
      list_all2 (\<lambda>A X. restrict A (fst (mmulti_join_pw A_pos A_neg L)) z \<in> X) A_pos (take (length A_pos) L) \<and>
      list_all2 (\<lambda>A X. restrict A (fst (mmulti_join_pw A_pos A_neg L)) z \<notin> X) A_neg (drop (length A_pos) L))"
proof -
  define L_pos where "L_pos = take (length A_pos) L"
  define L_neg where "L_neg = drop (length A_pos) L"
  have len: "length L = length A_pos + length A_neg"
    using list_all2_lengthD[OF assms(2)] by simp
  have len_pos: "length L_pos = length A_pos" and len_neg: "length L_neg = length A_neg"
    by (auto simp: L_pos_def L_neg_def len)
  have L: "L = L_pos @ L_neg"
    by (simp add: L_pos_def L_neg_def)
  have "list_all2 (\<lambda>A X. distinct A \<and> table A X) A_pos L_pos"
    "list_all2 (\<lambda>A X. distinct A \<and> table A X) A_neg L_neg"
    using assms(2) unfolding L list_all2_append[OF len_pos[symmetric]] by auto
  then have tabs: "\<forall>A X. (A, X) \<in> set (zip A_pos L_pos) \<longrightarrow> distinct A \<and> table A X"
    "\<forall>A X. (A, X) \<in> set (zip A_neg L_neg) \<longrightarrow> distinct A \<and> table A X"
    unfolding list_all2_iff by auto
  obtain A1 A_pos' where A_pos: "A_pos = A1 # A_pos'"
    using assms(1) by (cases A_pos) auto
  obtain t1 L_pos' where L_pos: "L_pos = t1 # L_pos'"
    using len_pos by (cases L_pos) (auto simp: A_pos)
  have len_pos': "length L_pos' = length A_pos'"
    using len_pos by (simp add: A_pos L_pos)
  have zip_pos: "zip A_pos L = (A1, t1) # zip A_pos' L_pos'"
    by (simp add: L A_pos L_pos zip_append2 len_pos')
  have tab1: "distinct A1" "table A1 t1"
    and tabs_pos': "\<forall>A X. (A, X) \<in> set (zip A_pos' L_pos') \<longrightarrow> distinct A \<and> table A X"
    using tabs(1) by (auto simp: A_pos L_pos)
  have cols: "set A1 \<union> (\<Union>BX \<in> set (zip A_pos' L_pos'). set (fst BX)) = (\<Union>A\<in>set A_pos. set A)"
    using len_pos' by (force simp: A_pos elim: in_set_impl_in_set_zip1[rotated, where ys=L_pos']
        dest: set_zip_leftD)
  obtain A' t' where pos: "mmulti_join_pos A1 t1 (zip A_pos' L_pos') = (A', t')"
    by fastforce
  note pos_corr = mmulti_join_pos_correct[OF tab1 tabs_pos', unfolded pos fst_conv snd_conv cols]
  have negs: "\<forall>A X. (A, X) \<in> set (zip A_neg L_neg) \<longrightarrow> distinct A \<and> table A X \<and> set A \<subseteq> set A'"
    using tabs(2) assms(3) pos_corr by (fastforce dest: set_zip_leftD)
  have pw: "mmulti_join_pw A_pos A_neg L = (A', mmulti_join_neg A' t' (zip A_neg L_neg))"
    by (simp add: zip_pos pos L_neg_def)
  note neg_corr = mmulti_join_neg_correct[OF conjunct1[OF pos_corr]
      conjunct1[OF conjunct2[OF conjunct2[OF pos_corr]]] negs]
  have pos_iff: "(restrict A1 A' z \<in> t1 \<and> (\<forall>A X. (A, X) \<in> set (zip A_pos' L_pos') \<longrightarrow> restrict A A' z \<in> X)) \<longleftrightarrow>
    list_all2 (\<lambda>A X. restrict A A' z \<in> X) A_pos L_pos" for z
    using len_pos' by (auto simp: A_pos L_pos list_all2_iff)
  have neg_iff: "(\<forall>A X. (A, X) \<in> set (zip A_neg L_neg) \<longrightarrow> restrict A A' z \<notin> X) \<longleftrightarrow>
    list_all2 (\<lambda>A X. restrict A A' z \<notin> X) A_neg L_neg" for z
    using len_neg by (auto simp: list_all2_iff)
  have z: "z \<in> mmulti_join_neg A' t' (zip A_neg L_neg) \<longleftrightarrow> wf_tuple A' z \<and>
    list_all2 (\<lambda>A X. restrict A A' z \<in> X) A_pos L_pos \<and> list_all2 (\<lambda>A X. restrict A A' z \<notin> X) A_neg L_neg"
    for z
    using conjunct2[OF neg_corr, rule_format, of z]
      conjunct2[OF conjunct2[OF conjunct2[OF pos_corr]], rule_format, of z]
    unfolding pos_iff[of z, symmetric] neg_iff[of z, symmetric] by blast
  show ?thesis
    unfolding pw fst_conv snd_conv L_pos_def[symmetric] L_neg_def[symmetric]
    using pos_corr neg_corr z by (intro conjI allI) simp_all
qed

lemma mmulti_join_correct:
  assumes "A_pos \<noteq> []"
      and "list_all2 (\<lambda>A X. distinct A \<and> table A X) (A_pos @ A_neg) L"
      and "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set A_pos. set A)"
      and "distinct cs" "set cs = (\<Union>A\<in>set A_pos. set A)"
  shows "z \<in> mmulti_join cs A_pos A_neg L \<longleftrightarrow> wf_tuple cs z \<and>
    list_all2 (\<lambda>A X. restrict A cs z \<in> X) A_pos (take (length A_pos) L) \<and>
    list_all2 (\<lambda>A X. restrict A cs z \<notin> X) A_neg (drop (length A_pos) L)"
proof -
  obtain cs' t where res: "(if use_generic_join then (mcols A_pos, mmulti_join_gen A_pos A_neg L)
    else mmulti_join_pw A_pos A_neg L) = (cs', t)"
    by fastforce
  have eq: "mmulti_join cs A_pos A_neg L = reorder cs cs' t"
    using res by (auto simp del: mmulti_join_gen.simps mmulti_join_pw.simps split: if_splits)
  have props: "distinct cs' \<and> set cs' = (\<Union>A\<in>set A_pos. set A) \<and> table cs' t \<and>
    (\<forall>z. z \<in> t \<longleftrightarrow> wf_tuple cs' z \<and>
      list_all2 (\<lambda>A X. restrict A cs' z \<in> X) A_pos (take (length A_pos) L) \<and>
      list_all2 (\<lambda>A X. restrict A cs' z \<notin> X) A_neg (drop (length A_pos) L))"
  proof (cases use_generic_join)
    case True
    with res have cs': "cs' = mcols A_pos" and t: "t = mmulti_join_gen A_pos A_neg L"
      by simp_all
    show ?thesis
      unfolding cs' t using mmulti_join_gen_correct[OF assms(1-3)]
      by (auto simp: table_def simp del: mmulti_join_gen.simps)
  next
    case False
    with res have "mmulti_join_pw A_pos A_neg L = (cs', t)"
      by simp
    then show ?thesis
      using mmulti_join_pw_correct[OF assms(1-3)] by (simp del: mmulti_join_pw.simps)
  qed
  have sub: "set A \<subseteq> set cs'" if "A \<in> set A_pos \<union> set A_neg" for A
    using that props assms(3) by auto
  have rr: "restrict A cs' (restrict cs' cs z) = restrict A cs z" if "A \<in> set A_pos \<union> set A_neg" for A
    using sub[OF that] by (simp add: restrict_restrict)
  have pos: "list_all2 (\<lambda>A X. restrict A cs' (restrict cs' cs z) \<in> X) A_pos (take (length A_pos) L) \<longleftrightarrow>
    list_all2 (\<lambda>A X. restrict A cs z \<in> X) A_pos (take (length A_pos) L)"
    by (rule list.rel_cong) (simp_all add: rr)
  have neg: "list_all2 (\<lambda>A X. restrict A cs' (restrict cs' cs z) \<notin> X) A_neg (drop (length A_pos) L) \<longleftrightarrow>
    list_all2 (\<lambda>A X. restrict A cs z \<notin> X) A_neg (drop (length A_pos) L)"
    by (rule list.rel_cong) (simp_all add: rr)
  have scs: "set cs = set cs'"
    using props assms(5) by simp
  show ?thesis
    unfolding eq mem_reorder[OF assms(4) conjunct1[OF props] scs conjunct1[OF conjunct2[OF conjunct2[OF props]]]]
      conjunct2[OF conjunct2[OF conjunct2[OF props]], rule_format] pos neg
    by simp
qed
(*<*)
end
(*>*)
