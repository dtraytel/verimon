(*<*)
theory Correct_Bin_Ops
  imports
    "MFODL_Monitor.Monitor" 
    Progress
begin
(*>*)


section \<open> Correctness \<close>


subsection \<open> Auxiliary list facts \<close>

lemma upt_append: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> [a..<b] @ [b..<c] = [a..<c]"
  by (metis le_Suc_ex upt_add_eq_append)

lemma list_all2_upt_append: "list_all2 P [a..<b] xs \<Longrightarrow> list_all2 P [b..<c] ys \<Longrightarrow>
  a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> list_all2 P [a..<c] (xs @ ys)"
  by (induction xs arbitrary: a) (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)

lemma list_all2_hdD:
  assumes "list_all2 P [i..<j] xs" "xs \<noteq> []"
  shows "P i (hd xs)" "i < j"
  using assms unfolding list_all2_conv_all_nth
  by (auto simp: hd_conv_nth intro: zero_less_diff[THEN iffD1] dest!: spec[of _ 0])

lemma list_all2_lastD:
  assumes "list_all2 P [i..<j] xs" "xs \<noteq> []"
  shows "P (j - 1) (last xs)"
  using assms list_all2_hdD(2)[OF assms, THEN less_imp_add_positive] unfolding list_all2_conv_all_nth
  by (auto dest!: spec[of _ "length xs - 1"] simp: last_conv_nth Suc_le_eq)

inductive list_all3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> bool" 
  for P :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool)" 
  where "list_all3 P [] [] []"
  | "P a1 a2 a3 \<Longrightarrow> list_all3 P q1 q2 q3 \<Longrightarrow> list_all3 P (a1 # q1) (a2 # q2) (a3 # q3)"

lemma list_all3_list_all2D: "list_all3 P xs ys zs \<Longrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  by (induct xs ys zs rule: list_all3.induct) auto

lemma list_all2_list_all3I: "length xs = length ys \<Longrightarrow> list_all2 (case_prod P) (zip xs ys) zs \<Longrightarrow>
  list_all3 P xs ys zs"
  by (induct xs ys arbitrary: zs rule: list_induct2)
    (auto simp: list_all2_Cons1 intro: list_all3.intros)

lemma list_all3_list_all2_eq: "list_all3 P xs ys zs \<longleftrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  using list_all2_list_all3I list_all3_list_all2D by blast

lemma list_all3_mapD: "list_all3 P (map f xs) (map g ys) (map h zs) \<Longrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  by (induct "map f xs" "map g ys" "map h zs" arbitrary: xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_mapI: "list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs \<Longrightarrow>
  list_all3 P (map f xs) (map g ys) (map h zs)"
  by (induct xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_map_iff: "list_all3 P (map f xs) (map g ys) (map h zs) \<longleftrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  using list_all3_mapD list_all3_mapI by blast

lemmas list_all3_map =
  list_all3_map_iff[where g=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and g=id, unfolded list.map_id id_apply]

lemma list_all3_conv_all_nth:
  "list_all3 P xs ys zs =
  (length xs = length ys \<and> length ys = length zs \<and> (\<forall>i < length xs. P (xs!i) (ys!i) (zs!i)))"
  by (auto simp add: list_all3_list_all2_eq list_all2_conv_all_nth)

lemma list_all3_refl [intro?]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P x x x) \<Longrightarrow> list_all3 P xs xs xs"
  by (simp add: list_all3_conv_all_nth)

lemma list_all3_list_all2_conv: "list_all3 R xs xs ys = list_all2 (\<lambda>x. R x x) xs ys"
  by (auto simp: list_all3_conv_all_nth list_all2_conv_all_nth)

lemma list_all3_Nil[simp]:
  "list_all3 P xs ys [] \<longleftrightarrow> xs = [] \<and> ys = []"
  "list_all3 P xs [] zs \<longleftrightarrow> xs = [] \<and> zs = []"
  "list_all3 P [] ys zs \<longleftrightarrow> ys = [] \<and> zs = []"
  unfolding list_all3_conv_all_nth by auto

lemma list_all3_Cons:
  "list_all3 P xs ys (z # zs) \<longleftrightarrow> (\<exists>x xs' y ys'. xs = x # xs' \<and> ys = y # ys' \<and> P x y z \<and> list_all3 P xs' ys' zs)"
  "list_all3 P xs (y # ys) zs \<longleftrightarrow> (\<exists>x xs' z zs'. xs = x # xs' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs' ys zs')"
  "list_all3 P (x # xs) ys zs \<longleftrightarrow> (\<exists>y ys' z zs'. ys = y # ys' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs ys' zs')"
  unfolding list_all3_conv_all_nth
  by (auto simp: length_Suc_conv Suc_length_conv nth_Cons split: nat.splits)

lemma list_all3_mono_strong: "list_all3 P xs ys zs \<Longrightarrow>
  (\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> P x y z \<Longrightarrow> Q x y z) \<Longrightarrow>
  list_all3 Q xs ys zs"
  by (induct xs ys zs rule: list_all3.induct) (auto intro: list_all3.intros)

lemma list_all3_list_all2I: "list_all3 (\<lambda>x y z. Q x z) xs ys zs \<Longrightarrow> list_all2 Q xs zs"
  by (induct xs ys zs rule: list_all3.induct) auto


subsection \<open> Monitor's binary buffers \<close>

definition wf_mbuf2 where
  "wf_mbuf2 i ja jb P Q buf \<longleftrightarrow> i \<le> ja \<and> i \<le> jb \<and> (case buf of (xs, ys) \<Rightarrow>
    list_all2 P [i..<ja] xs \<and> list_all2 Q [i..<jb] ys)"

lemma wf_mbuf2_add:
  assumes "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 P [ja..<ja'] xs"
    and "list_all2 Q [jb..<jb'] ys"
    and "ja \<le> ja'" "jb \<le> jb'"
  shows "wf_mbuf2 i ja' jb' P Q (mbuf2_add xs ys buf)"
  using assms unfolding wf_mbuf2_def
  by (auto 0 3 simp: list_all2_append2 upt_append dest: list_all2_lengthD
      intro: exI[where x="[i..<ja]"] exI[where x="[ja..<ja']"]
      exI[where x="[i..<jb]"] exI[where x="[jb..<jb']"] split: prod.splits)

lemma mbuf2_take_eqD:
  assumes "mbuf2_take f buf = (xs, buf')"
    and "wf_mbuf2 i ja jb P Q buf"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 (\<lambda>i z. \<exists>x y. P i x \<and> Q i y \<and> z = f x y) [i..<min ja jb] xs"
  using assms unfolding wf_mbuf2_def
  by (induction f buf arbitrary: i xs buf' rule: mbuf2_take.induct)
    (fastforce simp add: list_all2_Cons2 upt_eq_Cons_conv min_absorb1 min_absorb2 split: prod.splits)+

definition wf_mbuf2' :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
  ty Formula.formula \<Rightarrow> ty Formula.formula \<Rightarrow> event_data mbuf2 \<Rightarrow> bool" where
  "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf \<longleftrightarrow> wf_mbuf2 (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j))
    (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)
    (\<lambda>i (r). sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> r)
    (\<lambda>i (r). sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi> r) buf"

lemma wf_mbuf2'_0: "pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> wf_mbuf2' \<sigma> P V 0 n R \<phi> \<psi> ([], [])"
  unfolding wf_mbuf2'_def wf_mbuf2_def by simp

lemma mbuf2_take_add':
  assumes eq: "mbuf2_take f (mbuf2_add xs ys buf) = (zs, buf')"
    and pre: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and rm: "rel_mapping (\<le>) P P'"
    and xs: "list_all2 (\<lambda>i r. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i r. sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi> r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
  shows "wf_mbuf2' \<sigma> P' V j' n R \<phi> \<psi> buf'"
    and "list_all2 (\<lambda>i Z. \<exists>X Y.
      sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> X \<and>
      sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi> Y \<and>
      Z = f X Y)
      [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' \<psi> j')] zs"
  using pre rm unfolding wf_mbuf2'_def
  by (force intro!: mbuf2_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm])+

lemma mbuf2t_take_induct[consumes 5, case_names base step]:
  assumes "mbuf2t_take f z buf t nts = (z', buf', nt, nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
    and "U i z"
    and "\<And>k x y t z. i \<le> k \<Longrightarrow> Suc k \<le> ja \<Longrightarrow> Suc k \<le> jb \<Longrightarrow>
      P k x \<Longrightarrow> Q k y \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f x y t z)"
  shows "U (min ja jb) z'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf t nts arbitrary: i z' buf' nt nts' rule: mbuf2t_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated] split: prod.split)

lemma mbuf2t_take_add_induct'[consumes 6, case_names base step]:
  assumes eq: "mbuf2t_take f z (mbuf2_add xs ys buf) t nts = (z', buf', nt, nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"

    and pre_buf: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i (r). sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i (r). sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi> r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
    and base: "U (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) z"
    and step: "\<And>k X Y z. min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) \<le> k \<Longrightarrow>
      Suc k \<le> progress \<sigma> P' \<phi> j' \<Longrightarrow> Suc k \<le> progress \<sigma> P' \<psi> j' \<Longrightarrow>
      sat_table \<sigma> V n R (Formula.fv_list \<phi>) k \<phi> X \<Longrightarrow>
      sat_table \<sigma> V n R (Formula.fv_list \<psi>) k \<psi> Y \<Longrightarrow>      U k z \<Longrightarrow> U (Suc k) (f X Y (\<tau> \<sigma> k) z)"
  shows "U (min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' \<psi> j')) z'"
  using pre_buf pre_nts bounded rm unfolding wf_mbuf2'_def
  by (blast intro!: mbuf2t_take_induct[OF eq] wf_mbuf2_add[OF _ xs ys] 
      progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm]
      progress_le_gen base step)

lemma mbuf2t_take_nt:
  assumes "mbuf2t_take f z buf t nts = (z', buf', nt, nts')"
  shows "nt = hd (nts' @ rev nts @ [t])"
  using assms
  by (induction f z buf t nts arbitrary: z' buf' nt nts' rule: mbuf2t_take.induct)
     (auto simp add: hd_append split: list.splits if_splits)

lemma mbuf2t_take_eqD:
  assumes "mbuf2t_take f z buf t nts = (z', buf', nt, nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 R [min ja jb..<j] nts'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf t nts arbitrary: i z' buf' nt nts' rule: mbuf2t_take.induct)
     (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      split: prod.split)

definition wf_ts :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> ty Formula.formula \<Rightarrow> ty Formula.formula \<Rightarrow> ts list \<Rightarrow> bool" 
  where "wf_ts \<sigma> P j \<phi> \<psi> ts 
  \<longleftrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j] ts"

lemma wf_ts_0: "wf_ts \<sigma> P 0 \<phi> \<psi> []"
  unfolding wf_ts_def by simp

lemma mbuf2t_take_add':
  assumes eq: "mbuf2t_take f z (mbuf2_add xs ys buf) t nts = (z', buf', nt, nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and pre_buf: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i (r). sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i (r). sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi> r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
  shows "wf_mbuf2' \<sigma> P' V j' n R \<phi> \<psi> buf'"
    and "wf_ts \<sigma> P' j' \<phi> \<psi> nts'"
  using pre_buf pre_nts bounded rm unfolding wf_mbuf2'_def wf_ts_def
  by (auto intro!: mbuf2t_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm]
      progress_le_gen simp: progress_le_gen)


subsection \<open> Binary operators' qtable \<close>

text \<open>A disjunction's table is over its left operand's columns; the right operand's table is
  reordered to them.\<close>

lemma sat_table_union_reorder:
  assumes X: "sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> X"
    and Y: "sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi> Y"
    and fv: "Formula.fv \<phi> = Formula.fv \<psi>"
    and sat: "\<And>v. Formula.sat \<sigma> V v i \<chi> \<longleftrightarrow> Formula.sat \<sigma> V v i \<phi> \<or> Formula.sat \<sigma> V v i \<psi>"
  shows "sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<chi>
    (X \<union> reorder (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) Y)"
proof (rule qtable_union[OF X qtable_reorder_mem_restr[OF Y,
      where Q' = "\<lambda>v. Formula.sat \<sigma> V (val n (Formula.fv_list \<phi>) v) i \<psi>"]])
  show "set (Formula.fv_list \<phi>) = set (Formula.fv_list \<psi>)"
    using fv by simp
  show "Formula.sat \<sigma> V (val n (Formula.fv_list \<phi>) v) i \<psi> \<longleftrightarrow>
    Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) (restrict (Formula.fv_list \<psi>) (Formula.fv_list \<phi>) v)) i \<psi>" for v
    by (simp add: sat_restrict)
qed (use sat in simp_all)

text \<open>A formula bound to a predicate has the columns @{term "[0..<m]"}, in the order of
  @{const Formula.fv_list}; its tables are reordered to be read positionally.\<close>

lemma sat_table_reorder_upt:
  assumes X: "sat_table \<sigma> V m UNIV (Formula.fv_list \<phi>) i \<phi> X"
    and fv: "{0..<m} \<subseteq> fv \<phi>" "m = Formula.nfv \<phi>"
  shows "sat_table \<sigma> V m UNIV [0..<m] i \<phi> (reorder [0..<m] (Formula.fv_list \<phi>) X)"
proof (rule qtable_reorder_mem_restr[OF X])
  show "set [0..<m] = set (Formula.fv_list \<phi>)"
    using set_fv_list_nfv[OF fv] by simp
qed (simp_all add: sat_restrict)

lemma (in maux) qtable_bin_join:
  assumes "qtable A P1 Q1 X" "qtable B P2 Q2 Y" "distinct A" "distinct B"
    "\<not> b \<Longrightarrow> set B \<subseteq> set A" "C = cols_union A B"
    "\<And>x. wf_tuple C x \<Longrightarrow> P x \<Longrightarrow> P1 (restrict A C x) \<and> P2 (restrict B C x)"
    "\<And>x. b \<Longrightarrow> wf_tuple C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A C x) \<and> Q2 (restrict B C x)"
    "\<And>x. \<not> b \<Longrightarrow> wf_tuple C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A C x) \<and> \<not> Q2 (restrict B C x)"
  shows "qtable C P Q (bin_join A X b B Y)"
  using qtable_join[OF assms] bin_join_table[OF assms(3,4) qtableD(1)[OF assms(1)] qtableD(1)[OF assms(2)]]
  by simp

text \<open>The join of two tables restricted to a slice, in the slice.\<close>

lemma (in maux) qtable_bin_join_mem_restr:
  assumes "qtable A (mem_restr R A) Q1 X" "qtable B (mem_restr R B) Q2 Y" "distinct A" "distinct B"
    "\<not> b \<Longrightarrow> set B \<subseteq> set A" "C = cols_union A B"
    "\<And>x. b \<Longrightarrow> wf_tuple C x \<Longrightarrow> mem_restr R C x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A C x) \<and> Q2 (restrict B C x)"
    "\<And>x. \<not> b \<Longrightarrow> wf_tuple C x \<Longrightarrow> mem_restr R C x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A C x) \<and> \<not> Q2 (restrict B C x)"
  shows "qtable C (mem_restr R C) Q (bin_join A X b B Y)"
  using assms(6) by (intro qtable_bin_join[OF assms(1-6)] assms(7,8))
    (auto intro!: restrict_mem_restr simp: assms(3,4))

lemma (in maux) qtable_mmulti_join:
  assumes pos: "list_all3 (\<lambda>A Qi X. qtable A (mem_restr R A) Qi X \<and> distinct A) A_pos Q_pos L_pos"
    and neg: "list_all3 (\<lambda>A Qi X. qtable A (mem_restr R A) Qi X \<and> distinct A) A_neg Q_neg L_neg"
    and C: "distinct C" "set C = (\<Union>A\<in>set A_pos. set A)" and L_eq: "L = L_pos @ L_neg"
    and "A_pos \<noteq> []" and fv_subset: "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set A_pos. set A)"
    and Qs: "\<And>x. wf_tuple C x \<Longrightarrow> mem_restr R C x \<Longrightarrow> Q x \<longleftrightarrow>
      list_all2 (\<lambda>A Qi. Qi (restrict A C x)) A_pos Q_pos \<and>
      list_all2 (\<lambda>A Qi. \<not> Qi (restrict A C x)) A_neg Q_neg"
  shows "qtable C (mem_restr R C) Q (mmulti_join C A_pos A_neg L)"
proof (rule qtableI)
  from pos have 1: "list_all2 (\<lambda>A X. distinct A \<and> table A X) A_pos L_pos"
    by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth qtable_def)
  moreover from neg have "list_all2 (\<lambda>A X. distinct A \<and> table A X) A_neg L_neg"
    by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth qtable_def)
  ultimately have L: "list_all2 (\<lambda>A X. distinct A \<and> table A X) (A_pos @ A_neg) (L_pos @ L_neg)"
    by (rule list_all2_appendI)
  note in_join_iff = mmulti_join_correct[OF \<open>A_pos \<noteq> []\<close> L fv_subset C]
  from 1 have take_eq: "take (length A_pos) (L_pos @ L_neg) = L_pos"
    by (auto dest!: list_all2_lengthD)
  from 1 have drop_eq: "drop (length A_pos) (L_pos @ L_neg) = L_neg"
    by (auto dest!: list_all2_lengthD)
  have len: "length Q_pos = length A_pos" "length L_pos = length A_pos"
    "length Q_neg = length A_neg" "length L_neg = length A_neg"
    using pos neg by (auto simp: list_all3_conv_all_nth)
  have qpos: "restrict (A_pos ! i) C x \<in> L_pos ! i \<longleftrightarrow> (Q_pos ! i) (restrict (A_pos ! i) C x)"
    if "i < length A_pos" "mem_restr R C x" for i x
  proof -
    have q: "qtable (A_pos ! i) (mem_restr R (A_pos ! i)) (Q_pos ! i) (L_pos ! i)" "distinct (A_pos ! i)"
      using pos that(1) by (auto simp: list_all3_conv_all_nth)
    have "set (A_pos ! i) \<subseteq> set C"
      using that(1) C(2) nth_mem[OF that(1)] by blast
    then have "mem_restr R (A_pos ! i) (restrict (A_pos ! i) C x)"
      using restrict_mem_restr[OF that(2) C(1) q(2)] by simp
    with q(1) show ?thesis
      by (simp add: qtable_iff)
  qed
  have qneg: "restrict (A_neg ! i) C x \<in> L_neg ! i \<longleftrightarrow> (Q_neg ! i) (restrict (A_neg ! i) C x)"
    if "i < length A_neg" "mem_restr R C x" for i x
  proof -
    have q: "qtable (A_neg ! i) (mem_restr R (A_neg ! i)) (Q_neg ! i) (L_neg ! i)" "distinct (A_neg ! i)"
      using neg that(1) by (auto simp: list_all3_conv_all_nth)
    have "set (A_neg ! i) \<subseteq> set C"
      using that(1) C(2) fv_subset nth_mem[OF that(1)] by blast
    then have "mem_restr R (A_neg ! i) (restrict (A_neg ! i) C x)"
      using restrict_mem_restr[OF that(2) C(1) q(2)] by simp
    with q(1) show ?thesis
      by (simp add: qtable_iff)
  qed
  have sub: "mmulti_join C A_pos A_neg L \<subseteq> {x. wf_tuple C x \<and> list_all2 (\<lambda>A X. restrict A C x \<in> X) A_pos L_pos}"
    unfolding L_eq subset_iff in_join_iff take_eq by blast
  have finL: "\<forall>X \<in> set L_pos. finite X"
    using pos by (auto simp: list_all3_conv_all_nth in_set_conv_nth qtable_def)
  show "finite (mmulti_join C A_pos A_neg L)"
    by (rule finite_subset[OF sub finite_restrict_cover[OF C(1) _ finL]]) (simp add: C(2))
  show "table C (mmulti_join C A_pos A_neg L)"
    unfolding L_eq table_def by (simp add: in_join_iff)
  show "Q x" if "x \<in> mmulti_join C A_pos A_neg L" "wf_tuple C x" "mem_restr R C x" for x
    using that(2,3)
  proof (rule Qs[THEN iffD2, OF _ _ conjI])
    have pos': "list_all2 (\<lambda>A. (\<in>) (restrict A C x)) A_pos L_pos"
      and neg': "list_all2 (\<lambda>A. (\<notin>) (restrict A C x)) A_neg L_neg"
      using that(1) unfolding L_eq in_join_iff take_eq drop_eq by simp_all
    show "list_all2 (\<lambda>A Qi. Qi (restrict A C x)) A_pos Q_pos"
      using pos' qpos[OF _ that(3)] len by (auto simp: list_all2_conv_all_nth)
    show "list_all2 (\<lambda>A Qi. \<not> Qi (restrict A C x)) A_neg Q_neg"
      using neg' qneg[OF _ that(3)] len by (auto simp: list_all2_conv_all_nth)
  qed
  show "x \<in> mmulti_join C A_pos A_neg L" if "wf_tuple C x" "mem_restr R C x" "Q x" for x
    unfolding L_eq in_join_iff take_eq drop_eq
  proof (intro conjI)
    from that have pos': "list_all2 (\<lambda>A Qi. Qi (restrict A C x)) A_pos Q_pos"
      and neg': "list_all2 (\<lambda>A Qi. \<not> Qi (restrict A C x)) A_neg Q_neg"
      using Qs[THEN iffD1] by auto
    show "wf_tuple C x"
      by (rule that(1))
    show "list_all2 (\<lambda>A. (\<in>) (restrict A C x)) A_pos L_pos"
      using pos' qpos[OF _ that(2)] len by (auto simp: list_all2_conv_all_nth)
    show "list_all2 (\<lambda>A. (\<notin>) (restrict A C x)) A_neg L_neg"
      using neg' qneg[OF _ that(2)] len by (auto simp: list_all2_conv_all_nth)
  qed
qed(*<*)
end
(*>*)