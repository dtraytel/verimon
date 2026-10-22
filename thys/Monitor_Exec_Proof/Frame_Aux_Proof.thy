(*<*)
theory Frame_Aux_Proof
  imports "Monitor_Exec.Frame_Aux" Frame_Proof "MFODL_Monitor_Proof.Correctness" "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



section \<open>The executable Since and Until structures\<close>

text \<open>
  The temporal structures run over the ascending columns @{term "eargs cs_R cs_L args"}: a stored
  tuple is a tuple over the right operand's columns @{term cs_R}, and the probe table is the left
  operand's, over @{term cs_L}.  The kernel's structures read the probe at a stored tuple by
  restricting the latter to the left operand's columns; over ascending columns that restriction
  is the executable projection at the mask @{term "mrg_left_key (mrg_plan cs_R cs_L)"}, which is a
  single pass over the tuple.  This theory adds an index on that projection and proves the
  resulting structures equal to the verified ones.
\<close>

subsection \<open>The executable index under the semi-join\<close>

text \<open>
  Restricting the index to the surviving keys is the index of the surviving tuples: a bucket
  passes or fails as a whole, because the filter only looks at the key.
\<close>

lemma eidx_filter:
  "Mapping.filter (\<lambda>k _. (k \<in> X) = pos) (eidx msk T) = eidx msk (esemi msk pos T X)"
proof -
  have "Mapping.lookup (Mapping.filter (\<lambda>k _. (k \<in> X) = pos) (eidx msk T)) k
      = Mapping.lookup (eidx msk (esemi msk pos T X)) k" for k
  proof -
    have img: "(k \<in> eproj msk ` esemi msk pos T X) = (k \<in> eproj msk ` T \<and> (k \<in> X) = pos)"
      by (auto simp: esemi_def)
    have bucket: "(k \<in> X) = pos \<Longrightarrow> {y \<in> esemi msk pos T X. eproj msk y = k}
        = {y \<in> T. eproj msk y = k}"
      by (auto simp: esemi_def)
    show ?thesis
      using bucket by (simp add: Mapping.lookup_filter lookup_eidx img)
  qed
  then show ?thesis by (simp add: mapping_eqI)
qed

subsection \<open>Maintaining the index incrementally\<close>

text \<open>
  The structure adds and removes whole tables at a time, so the index is maintained by combining
  it with the index of the added table, and by subtracting the index of the removed one bucket by
  bucket.
\<close>

lemma eidx_empty[simp]: "eidx msk {} = Mapping.empty"
  by (intro mapping_eqI) (simp add: lookup_eidx)

text \<open>Only the buckets that the subtrahend touches are dropped when they empty: a bucket at a key
  the subtrahend does not have is left as it is.  On a clustering, which has no empty buckets, the
  two readings agree; the executable version of the subtraction, which only visits the
  subtrahend's keys, realises this one exactly.\<close>

subsection \<open>The mask of the left operand's columns among the right operand's\<close>

lemma length_mrg_left_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     length (mrg_left_key (mrg_plan cs1 cs2)) = length cs1"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

lemma mrg_left_key_MRgt: "mrg_left_key (map (\<lambda>_. MRgt) ds) = []"
  by (induct ds) auto

lemma mrg_plan_Cons_cases:
  fixes c d :: nat
  assumes "sorted_wrt (<) (c # cs)" "sorted_wrt (<) (d # ds)" "set (d # ds) \<subseteq> set (c # cs)"
  shows "\<not> d < c" and "c < d \<Longrightarrow> set (d # ds) \<subseteq> set cs" and "c = d \<Longrightarrow> set ds \<subseteq> set cs"
proof -
  have d: "d \<in> set (c # cs)" using assms(3) by simp
  then show "\<not> d < c" using assms(1) by auto
  show "set (d # ds) \<subseteq> set cs" if cd: "c < d"
  proof
    fix x assume x: "x \<in> set (d # ds)"
    then have "c < x" using cd assms(2) by (auto intro: less_trans)
    then show "x \<in> set cs" using x assms(3) by auto
  qed
  show "set ds \<subseteq> set cs" if cd: "c = d"
    using assms(2,3) cd by auto
qed

lemma mrg_left_key_all_False:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     (\<forall>i \<in> set (mrg_left_key (mrg_plan cs1 cs2)). \<not> i) = (cs2 = [])"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: mrg_left_key_MRgt)
next
  case (2 c cs)
  then show ?case by simp
next
  case (3 c cs d ds)
  note cc = mrg_plan_Cons_cases[OF 3(4,5,6)]
  show ?case
  proof (cases "c < d")
    case True
    then show ?thesis using 3(1)[OF True] 3(4,5) cc(2)[OF True] by simp
  next
    case False
    then have "c = d" using cc(1) by simp
    then show ?thesis by simp
  qed
qed

lemma mrg_left_key_all_True:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     (\<forall>i \<in> set (mrg_left_key (mrg_plan cs1 cs2)). i) = (cs2 = cs1)"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: mrg_left_key_MRgt)
next
  case (2 c cs)
  then show ?case by simp
next
  case (3 c cs d ds)
  note cc = mrg_plan_Cons_cases[OF 3(4,5,6)]
  show ?case
  proof (cases "c < d")
    case True
    then show ?thesis by simp
  next
    case False
    then have e: "c = d" using cc(1) by simp
    then show ?thesis using 3(3)[OF False cc(1)] 3(4,5) cc(3)[OF e] False by simp
  qed
qed

lemma emsk_args_dproj:
  assumes dm: "emsk_args args msk" and l: "length as = length (args_R args)"
  shows "eproj msk as = restrict (args_L args) (args_R args) as"
proof -
  let ?R = "args_R args" and ?L = "args_L args"
  have sR: "sorted_wrt (<) ?R" and sL: "sorted_wrt (<) ?L" and sub: "set ?L \<subseteq> set ?R"
    and m: "msk = mrg_left_key (mrg_plan ?R ?L)" using dm by (auto simp: emsk_args_def)
  have fR: "eframe ?R ?R" and fL: "eframe ?L ?L"
    using sR sL by (auto simp: eframe_def strict_sorted_iff)
  have w: "wf_tuple ?R as" using l by (simp add: wf_tuple_def)
  have "eproj msk (restrict ?R ?R as) = restrict ?L ?L (restrict ?L ?R as)"
    unfolding m by (rule eproj_left_key_eq[OF fR fL sub])
  then show ?thesis
    using restrict_idle[OF eframeD(1)[OF fR] w]
      restrict_idle[OF eframeD(1)[OF fL] wf_tuple_restrict[of ?L ?R as]] by simp
qed

lemma emsk_args_empty: "emsk_args args msk \<Longrightarrow> (args_L args = []) = (\<forall>i \<in> set msk. \<not> i)"
  by (simp add: emsk_args_def mrg_left_key_all_False)

lemma emsk_args_full: "emsk_args args msk \<Longrightarrow> (args_L args = args_R args) = (\<forall>i \<in> set msk. i)"
  by (simp add: emsk_args_def mrg_left_key_all_True)

lemma emsk_args_dargs:
  assumes "sorted_wrt (<) cs_R" "sorted_wrt (<) cs_L" "set cs_L \<subseteq> set cs_R"
  shows "emsk_args (eargs cs_R cs_L args) (mrg_left_key (mrg_plan cs_R cs_L))"
  using assms by (simp add: emsk_args_def)

text \<open>
  Both indexed tables are determined by the mapping they index, so normalising them away does not
  leave the invariant.
\<close>

lemma valid_mmsaux_norm: "valid_mmsaux args cur aux ys \<Longrightarrow>
    valid_mmsaux args cur (mmsaux_norm args aux) ys"
  by (cases aux) (auto simp: wf_table_sig_args wf_table_of_set_args)

lemma emsk_args_length: "emsk_args args msk \<Longrightarrow> length msk = length (args_R args)"
  by (simp add: emsk_args_def length_mrg_left_key)

subsection \<open>What the window's entry and exit do to the keys\<close>

text \<open>
  The two folds that move tables out of and into the window report the tuples they removed and
  added.  That report is exactly the difference between the old and the new key set, which is what
  the index has to be reduced by and combined with.
\<close>

lemma fold_filter_set_keys:
  "fold filter_set ds (m, Y) = (m', Y') \<Longrightarrow> Y \<inter> Mapping.keys m = {} \<Longrightarrow>
     Mapping.keys m' = Mapping.keys m - Y' \<and> Y \<subseteq> Y'"
proof (induct ds arbitrary: m Y)
  case (Cons a ds)
  obtain t X where a: "a = (t, X)" by (cases a)
  define m'' where "m'' = Mapping.filter (filter_cond X m t) m"
  define Y'' where "Y'' = Y \<union> (Mapping.keys m - Mapping.keys m'')"
  have step: "filter_set a (m, Y) = (m'', Y'')"
    by (simp add: a filter_set.simps Let_def m''_def Y''_def)
  have sub: "Mapping.keys m'' \<subseteq> Mapping.keys m"
    by (auto simp: m''_def Mapping_keys_filter)
  have dis: "Y'' \<inter> Mapping.keys m'' = {}"
    using Cons(3) sub by (auto simp: Y''_def)
  have f: "fold filter_set ds (m'', Y'') = (m', Y')" using Cons(2) step by simp
  have IH: "Mapping.keys m' = Mapping.keys m'' - Y' \<and> Y'' \<subseteq> Y'" by (rule Cons(1)[OF f dis])
  show ?case using IH sub by (auto simp: Y''_def)
qed auto

lemma fold_upd_set_keys_keys:
  "fold (upd_set_keys Z) ds (m, Y) = (m', Y') \<Longrightarrow> Y \<subseteq> Mapping.keys m \<Longrightarrow>
     Mapping.keys m' = Mapping.keys m \<union> Y' \<and> Y \<subseteq> Y'"
proof (induct ds arbitrary: m Y)
  case (Cons a ds)
  obtain t X where a: "a = (t, X)" by (cases a)
  define A where "A = Z X t"
  have step: "upd_set_keys Z a (m, Y) = (upd_set m (\<lambda>_. t) A, Y \<union> A)"
    by (simp add: a upd_set_keys.simps A_def)
  have k: "Mapping.keys (upd_set m (\<lambda>_. t) A) = Mapping.keys m \<union> A"
    by (simp add: Mapping_upd_set_keys)
  have f: "fold (upd_set_keys Z) ds (upd_set m (\<lambda>_. t) A, Y \<union> A) = (m', Y')"
    using Cons(2) step by simp
  have sub: "Y \<union> A \<subseteq> Mapping.keys (upd_set m (\<lambda>_. t) A)" using Cons(3) k by auto
  have IH: "Mapping.keys m' = Mapping.keys (upd_set m (\<lambda>_. t) A) \<union> Y' \<and> Y \<union> A \<subseteq> Y'"
    by (rule Cons(1)[OF f sub])
  show ?case using IH k by auto
qed auto

lemma fold_filter_set_keys':
  "fold filter_set ds (m, {}) = (m', Y') \<Longrightarrow> Mapping.keys m' = Mapping.keys m - Y'"
  using fold_filter_set_keys[of ds m "{}" m' Y'] by simp

lemma fold_upd_set_keys_keys':
  "fold (upd_set_keys Z) ds (m, {}) = (m', Y') \<Longrightarrow> Mapping.keys m' = Mapping.keys m \<union> Y'"
  using fold_upd_set_keys_keys[of Z ds m "{}" m' Y'] by simp

subsection \<open>The executable operations are the verified ones\<close>

lemma emsaux_cases:
  fixes daux :: "'a emsaux"
  obtains t gc msk data_prev data_in table_in idx_in tuple_in idx_since tuple_since
  where "daux = (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
    idx_since, tuple_since)"
  by (metis prod.collapse)

lemma emsaux_of_dinit: "emsaux_of args (einit_msaux args msk) = init_mmsaux args"
  by (simp add: einit_msaux_def wf_table_of_set_args_def)

lemma emsaux_inv_dinit: "emsaux_inv args msk (einit_msaux args msk)"
  by (simp add: einit_msaux_def)

lemma valid_einit_msaux:
  assumes "set L \<subseteq> set R" "distinct L" "distinct R"
  shows "valid_emsaux (init_args I n L R b agg) msk 0
    (einit_msaux (init_args I n L R b agg) msk) []"
  unfolding valid_emsaux_def emsaux_of_dinit
  by (rule conjI[OF valid_init_mmsaux[OF assms] emsaux_inv_dinit])

lemma emsaux_of_eshift_end:
  "emsaux_of args (eshift_end args nt daux)
   = mmsaux_norm args (shift_end args nt (emsaux_of args daux))"
  by (cases daux rule: emsaux_cases) (simp add: Let_def split: prod.splits)

lemma emsaux_inv_eshift_end:
  assumes "emsaux_inv args msk daux"
  shows "emsaux_inv args msk (eshift_end args nt daux)"
proof (cases daux rule: emsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  show ?thesis
    using assms unfolding 1
    by (auto simp: Let_def eidx_upd_def eidx_minus_eq split: prod.splits
        dest!: fold_filter_set_keys')
qed

lemma valid_dmsauxI:
  assumes "valid_mmsaux args cur aux ys"
    and "emsaux_of args daux = mmsaux_norm args aux"
    and "emsaux_inv args msk daux"
  shows "valid_emsaux args msk cur daux ys"
  unfolding valid_emsaux_def assms(2)
  by (rule conjI[OF valid_mmsaux_norm[OF assms(1)] assms(3)])

lemma valid_dmsauxD:
  "valid_emsaux args msk cur daux ys \<Longrightarrow> valid_mmsaux args cur (emsaux_of args daux) ys"
  by (simp add: valid_emsaux_def)

lemma valid_emsaux_inv: "valid_emsaux args msk cur daux ys \<Longrightarrow> emsaux_inv args msk daux"
  by (simp add: valid_emsaux_def)

lemma valid_eshift_end:
  assumes "valid_emsaux args msk cur daux ys" and "nt \<ge> cur"
  shows "valid_emsaux args msk cur (eshift_end args nt daux)
     (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) ys)"
  by (rule valid_dmsauxI[OF valid_shift_end_mmsaux[OF valid_dmsauxD[OF assms(1)] assms(2)]
      emsaux_of_eshift_end emsaux_inv_eshift_end[OF valid_emsaux_inv[OF assms(1)]]])

lemma emsaux_of_dadd_new_ts':
  "emsaux_of args (eadd_new_ts_msaux' args nt daux)
   = mmsaux_norm args (add_new_ts_mmsaux' args nt (emsaux_of args daux))"
  by (cases daux rule: emsaux_cases) (simp add: Let_def split: prod.splits)

lemma emsaux_inv_dadd_new_ts':
  assumes "emsaux_inv args msk daux"
  shows "emsaux_inv args msk (eadd_new_ts_msaux' args nt daux)"
proof (cases daux rule: emsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  show ?thesis
    using assms unfolding 1
    by (auto simp: Let_def eidx_upd_def eidx_union_eq split: prod.splits
        dest!: fold_upd_set_keys_keys')
qed

lemma valid_dadd_new_ts':
  assumes "valid_emsaux args msk cur daux ys" and "nt \<ge> cur"
  shows "valid_emsaux args msk nt (eadd_new_ts_msaux' args nt daux) ys"
  by (rule valid_dmsauxI[OF valid_add_new_ts_mmsaux'[OF valid_dmsauxD[OF assms(1)] assms(2)]
      emsaux_of_dadd_new_ts' emsaux_inv_dadd_new_ts'[OF valid_emsaux_inv[OF assms(1)]]])

lemma valid_dadd_new_ts:
  assumes "valid_emsaux args msk cur daux ys" and "nt \<ge> cur"
  shows "valid_emsaux args msk nt (eadd_new_ts_msaux args nt daux)
     (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) ys)"
  unfolding eadd_new_ts_msaux_def
  by (rule valid_dadd_new_ts'[OF valid_eshift_end[OF assms] assms(2)])

lemma emsaux_of_dgc:
  "emsaux_of args (egc_msaux args daux) = mmsaux_norm args (gc_mmsaux args (emsaux_of args daux))"
  by (cases daux rule: emsaux_cases) (simp add: Let_def)

lemma emsaux_inv_dgc:
  "emsaux_inv args msk daux \<Longrightarrow> emsaux_inv args msk (egc_msaux args daux)"
  by (cases daux rule: emsaux_cases) (simp add: Let_def eidx_upd_def)

lemma valid_dgc:
  assumes "valid_emsaux args msk cur daux ys"
  shows "valid_emsaux args msk cur (egc_msaux args daux) ys"
  by (rule valid_dmsauxI[OF valid_gc_mmsaux[OF valid_dmsauxD[OF assms]]
      emsaux_of_dgc emsaux_inv_dgc[OF valid_emsaux_inv[OF assms]]])

lemma emsaux_of_dadd_new_table:
  "emsaux_of args (eadd_new_table_msaux args X daux)
   = mmsaux_norm args (add_new_table_mmsaux args X (emsaux_of args daux))"
  by (cases daux rule: emsaux_cases) (simp add: Let_def)

lemma emsaux_inv_dadd_new_table:
  "emsaux_inv args msk daux \<Longrightarrow> emsaux_inv args msk (eadd_new_table_msaux args X daux)"
  by (cases daux rule: emsaux_cases)
     (simp add: Let_def eidx_upd_def eidx_union_eq Mapping_upd_set_keys)

lemma valid_dadd_new_table:
  assumes "valid_emsaux args msk cur daux ys" and "table (args_R args) X"
  shows "valid_emsaux args msk cur (eadd_new_table_msaux args X daux)
    (case ys of [] \<Rightarrow> [(cur, X)]
     | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # ys)"
  by (rule valid_dmsauxI[OF valid_add_new_table_mmsaux[OF valid_dmsauxD[OF assms(1)] assms(2)]
      emsaux_of_dadd_new_table emsaux_inv_dadd_new_table[OF valid_emsaux_inv[OF assms(1)]]])

lemma eresult_msaux_eq: "eresult_msaux args daux = result_mmsaux args (emsaux_of args daux)"
  by (cases daux rule: emsaux_cases) simp

lemma valid_eresult_msaux:
  "valid_emsaux args msk cur daux ys \<Longrightarrow> eresult_msaux args daux
    = foldr (\<union>) [rel. (t, rel) \<leftarrow> ys, memL (args_ivl args) (cur - t)] {}"
  by (simp add: eresult_msaux_eq valid_result_mmsaux[OF valid_dmsauxD])

subsection \<open>The join is the verified join\<close>

lemma eproj_all_False: "\<forall>i \<in> set msk. \<not> i \<Longrightarrow> length as = length msk \<Longrightarrow> eproj msk as = []"
  by (induct msk as rule: eproj.induct) auto

lemma eproj_all_True_mask: "\<forall>i \<in> set msk. i \<Longrightarrow> length as = length msk \<Longrightarrow> eproj msk as = as"
  by (induct msk as rule: eproj.induct) auto

lemma Mapping_filter_True: "Mapping.filter (\<lambda>_ _. True) m = m"
  by (intro mapping_eqI) (simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_filter_False: "Mapping.filter (\<lambda>_ _. False) m = Mapping.empty"
  by (intro mapping_eqI) (simp add: Mapping.lookup_filter split: option.splits)

lemma mapping_delete_set_filter:
  "D = {as \<in> Mapping.keys m. \<not> P as} \<Longrightarrow> mapping_delete_set m D = Mapping.filter (\<lambda>as _. P as) m"
  by (intro mapping_eqI)
     (auto simp: delete_set_lookup Mapping.lookup_filter Mapping.keys_dom_lookup
       split: option.splits)

text \<open>
  Whichever branch it takes, the executable join filters both mappings by the executable test, and the
  window's table follows the mapping it indexes.  That is the verified join's abstract form
  (@{const join_mmsaux_abs}).
\<close>

lemma ejoin_msaux_abs:
  assumes v: "valid_emsaux args msk cur (t, gc, m, dp, di, ti, ii, tui, idxs, tus) ys"
    and dm: "emsk_args args msk"
  shows "emsaux_of args (ejoin_msaux args Y (t, gc, m, dp, di, ti, ii, tui, idxs, tus))
     = join_mmsaux_abs args Y (emsaux_of args (t, gc, m, dp, di, ti, ii, tui, idxs, tus))"
proof -
  have vm: "valid_mmsaux args cur (emsaux_of args (t, gc, m, dp, di, ti, ii, tui, idxs, tus)) ys"
    by (rule valid_dmsauxD[OF v])
  have mm: "m = msk" using valid_emsaux_inv[OF v] by simp
  have lm: "length msk = length (args_R args)" by (rule emsk_args_length[OF dm])
  have ti_keys: "ti = Mapping.keys tui"
    and tab_in: "table (args_R args) (Mapping.keys tui)"
    and tab_since: "table (args_R args) (Mapping.keys tus)"
    using vm by simp_all
  have len_in: "length as = length (args_R args)" if "as \<in> Mapping.keys tui" for as
    using tab_in that by (auto simp: table_def wf_tuple_def)
  have len_since: "length as = length (args_R args)" if "as \<in> Mapping.keys tus" for as
    using tab_since that by (auto simp: table_def wf_tuple_def)
  have fin: "Mapping.filter (\<lambda>as _. join_cond (args_pos args) Y
        (restrict (args_L args) (args_R args) as)) tui
      = Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tui"
    by (rule Mapping_filter_cong) (simp add: join_cond_eq emsk_args_dproj[OF dm len_in])
  have fsince: "Mapping.filter (\<lambda>as _. join_cond (args_pos args) Y
        (restrict (args_L args) (args_R args) as)) tus
      = Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tus"
    by (rule Mapping_filter_cong) (simp add: join_cond_eq emsk_args_dproj[OF dm len_since])
  show ?thesis
  proof (cases "\<forall>i \<in> set msk. \<not> i")
    case True
    have cin: "Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tui
        = (if ([] \<in> Y) = args_pos args then tui else Mapping.empty)"
    proof -
      have "Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tui
          = Mapping.filter (\<lambda>as _. ([] \<in> Y) = args_pos args) tui"
        by (rule Mapping_filter_cong) (simp add: eproj_all_False[OF True] len_in lm)
      then show ?thesis
        by (cases "([] \<in> Y) = args_pos args")
           (simp_all add: Mapping_filter_True Mapping_filter_False)
    qed
    have csince: "Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tus
        = (if ([] \<in> Y) = args_pos args then tus else Mapping.empty)"
    proof -
      have "Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tus
          = Mapping.filter (\<lambda>as _. ([] \<in> Y) = args_pos args) tus"
        by (rule Mapping_filter_cong) (simp add: eproj_all_False[OF True] len_since lm)
      then show ?thesis
        by (cases "([] \<in> Y) = args_pos args")
           (simp_all add: Mapping_filter_True Mapping_filter_False)
    qed
    show ?thesis
      using True unfolding mm by (auto simp: Let_def fin fsince cin csince ti_keys wf_table_of_set_args_def)
  next
    case False
    note noneF = False
    show ?thesis
    proof (cases "\<forall>i \<in> set msk. i")
      case True
      have cin: "Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tui
          = Mapping.filter (\<lambda>as _. (as \<in> Y) = args_pos args) tui"
        by (rule Mapping_filter_cong) (simp add: eproj_all_True_mask[OF True] len_in lm)
      have csince: "Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tus
          = Mapping.filter (\<lambda>as _. (as \<in> Y) = args_pos args) tus"
        by (rule Mapping_filter_cong) (simp add: eproj_all_True_mask[OF True] len_since lm)
      have d: "(if args_pos args then ti - Y else ti \<inter> Y)
          = {as \<in> Mapping.keys tui. \<not> ((as \<in> Y) = args_pos args)}"
        unfolding ti_keys by auto
      have e: "mapping_delete_set tui (if args_pos args then ti - Y else ti \<inter> Y)
          = Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tui"
        unfolding cin by (rule mapping_delete_set_filter[OF d])
      have f: "ti - (if args_pos args then ti - Y else ti \<inter> Y)
          = Mapping.keys (Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tui)"
        unfolding e[symmetric] ti_keys by simp
      show ?thesis
        using noneF True unfolding mm
        by (auto simp: Let_def fin fsince e f csince[symmetric])
    next
      case False
      have live: "eidx_live args"
        using noneF False emsk_args_empty[OF dm] emsk_args_full[OF dm]
        by (simp add: eidx_live_def)
      have ixin: "ii = eidx msk (Mapping.keys tui)"
        and ixs: "idxs = eidx msk (Mapping.keys tus)"
        using valid_emsaux_inv[OF v] live by simp_all
      have din: "esemi_idx msk (\<not> args_pos args) ii Y
          = {as \<in> Mapping.keys tui. \<not> ((eproj msk as \<in> Y) = args_pos args)}"
        unfolding ixin esemi_idx_dsemi by (auto simp: esemi_def)
      have ds: "esemi_idx msk (\<not> args_pos args) idxs Y
          = {as \<in> Mapping.keys tus. \<not> ((eproj msk as \<in> Y) = args_pos args)}"
        unfolding ixs esemi_idx_dsemi by (auto simp: esemi_def)
      have e: "mapping_delete_set tui (esemi_idx msk (\<not> args_pos args) ii Y)
          = Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tui"
        by (rule mapping_delete_set_filter[OF din])
      have e': "mapping_delete_set tus (esemi_idx msk (\<not> args_pos args) idxs Y)
          = Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tus"
        by (rule mapping_delete_set_filter[OF ds])
      have f: "ti - esemi_idx msk (\<not> args_pos args) ii Y
          = Mapping.keys (Mapping.filter (\<lambda>as _. (eproj msk as \<in> Y) = args_pos args) tui)"
        unfolding e[symmetric] ti_keys by simp
      show ?thesis
        using noneF False unfolding mm
        by (auto simp: Let_def fin fsince e e' f)
    qed
  qed
qed

lemma emsaux_inv_djoin:
  assumes v: "valid_emsaux args msk cur (t, gc, m, dp, di, ti, ii, tui, idxs, tus) ys"
    and dm: "emsk_args args msk"
  shows "emsaux_inv args msk (ejoin_msaux args Y (t, gc, m, dp, di, ti, ii, tui, idxs, tus))"
proof (cases "\<forall>i \<in> set msk. \<not> i")
  case True
  then have "\<not> eidx_live args" using emsk_args_empty[OF dm] by (auto simp: eidx_live_def)
  then show ?thesis using valid_emsaux_inv[OF v] True by (simp add: Let_def)
next
  case False
  note noneF = False
  show ?thesis
  proof (cases "\<forall>i \<in> set msk. i")
    case True
    then have "\<not> eidx_live args" using emsk_args_full[OF dm] by (auto simp: eidx_live_def)
    then show ?thesis using valid_emsaux_inv[OF v] noneF True by (simp add: Let_def)
  next
    case False
    have live: "eidx_live args"
      using noneF False emsk_args_empty[OF dm] emsk_args_full[OF dm] by (simp add: eidx_live_def)
    have mm: "m = msk" using valid_emsaux_inv[OF v] by simp
    have ixin: "ii = eidx msk (Mapping.keys tui)"
      and ixs: "idxs = eidx msk (Mapping.keys tus)"
      using valid_emsaux_inv[OF v] live by simp_all
    have fi: "Mapping.filter (\<lambda>k _. (k \<in> Y) = args_pos args) ii
        = eidx msk (esemi msk (args_pos args) (Mapping.keys tui) Y)"
      unfolding ixin by (rule eidx_filter)
    have fs: "Mapping.filter (\<lambda>k _. (k \<in> Y) = args_pos args) idxs
        = eidx msk (esemi msk (args_pos args) (Mapping.keys tus) Y)"
      unfolding ixs by (rule eidx_filter)
    have ki: "Mapping.keys tui - esemi_idx msk (\<not> args_pos args) ii Y
        = esemi msk (args_pos args) (Mapping.keys tui) Y"
      unfolding ixin esemi_idx_dsemi by (auto simp: esemi_def)
    have ks: "Mapping.keys tus - esemi_idx msk (\<not> args_pos args) idxs Y
        = esemi msk (args_pos args) (Mapping.keys tus) Y"
      unfolding ixs esemi_idx_dsemi by (auto simp: esemi_def)
    show ?thesis
      using noneF False unfolding mm by (auto simp: Let_def fi fs ki ks)
  qed
qed

subsection \<open>The join's validity\<close>

lemma mmsaux_cases:
  fixes aux :: "'a mmsaux"
  obtains nt gc data_prev data_in table_in wf_table_in tuple_in wf_table_since tuple_since
  where "aux = (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in,
    wf_table_since, tuple_since)"
  by (metis prod.collapse)

lemma join_mmsaux_abs_eq':
  assumes "valid_mmsaux args cur aux auxlist" and "table (args_L args) X"
  shows "join_mmsaux args X aux = join_mmsaux_abs args X aux"
proof (cases aux rule: mmsaux_cases)
  case (1 nt gc dp di ti wi tui ws tus)
  show ?thesis unfolding 1
    by (rule join_mmsaux_abs_eq[OF assms(1)[unfolded 1] assms(2)])
qed

lemma mmsaux_norm_join_mmsaux_abs:
  "mmsaux_norm args (join_mmsaux_abs args X aux) = join_mmsaux_abs args X aux"
  by (cases aux rule: mmsaux_cases) (simp add: Let_def)

lemma valid_djoin:
  assumes v: "valid_emsaux args msk cur daux ys" and dm: "emsk_args args msk"
    and tY: "table (args_L args) Y"
  shows "valid_emsaux args msk cur (ejoin_msaux args Y daux)
     (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) Y)) ys)"
proof (cases daux rule: emsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  have vm: "valid_mmsaux args cur (emsaux_of args daux) ys" by (rule valid_dmsauxD[OF v])
  have abs: "emsaux_of args (ejoin_msaux args Y daux)
      = join_mmsaux_abs args Y (emsaux_of args daux)"
    using ejoin_msaux_abs[OF v[unfolded 1] dm] unfolding 1 .
  have eq: "emsaux_of args (ejoin_msaux args Y daux)
      = mmsaux_norm args (join_mmsaux args Y (emsaux_of args daux))"
    unfolding abs join_mmsaux_abs_eq'[OF vm tY] mmsaux_norm_join_mmsaux_abs ..
  have inv: "emsaux_inv args msk (ejoin_msaux args Y daux)"
    using emsaux_inv_djoin[OF v[unfolded 1] dm] unfolding 1 .
  show ?thesis
    by (rule valid_dmsauxI[OF valid_join_mmsaux[OF vm tY] eq inv])
qed

lemma valid_dgc_join:
  assumes v: "valid_emsaux args msk cur daux ys" and dm: "emsk_args args msk"
    and tY: "table (args_L args) Y"
  shows "valid_emsaux args msk cur (egc_join_msaux args Y daux)
     (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) Y)) ys)"
proof -
  have alt: "egc_join_msaux args Y daux = ejoin_msaux args Y (egc_msaux args daux)
      \<or> egc_join_msaux args Y daux = ejoin_msaux args Y daux"
    by (cases daux rule: emsaux_cases) auto
  show ?thesis
    using alt
  proof
    assume "egc_join_msaux args Y daux = ejoin_msaux args Y (egc_msaux args daux)"
    then show ?thesis using valid_djoin[OF valid_dgc[OF v] dm tY] by simp
  next
    assume "egc_join_msaux args Y daux = ejoin_msaux args Y daux"
    then show ?thesis using valid_djoin[OF v dm tY] by simp
  qed
qed

lemma valid_emsaux_lz_intro:
  "valid_emsaux args msk cur daux ys \<Longrightarrow> (memL (args_ivl args) 0 \<Longrightarrow> linearize (eprev_of daux) = [])
    \<Longrightarrow> valid_emsaux_lz args msk cur daux ys"
  unfolding valid_emsaux_lz_def by (cases daux rule: emsaux_cases) (simp, metis)

lemma valid_einit_msaux_lz:
  assumes "set L \<subseteq> set R" "distinct L" "distinct R"
  shows "valid_emsaux_lz (init_args I n L R b agg) msk 0
    (einit_msaux (init_args I n L R b agg) msk) []"
  by (rule valid_emsaux_lz_intro[OF valid_einit_msaux[OF assms]])
    (simp add: einit_msaux_def empty_queue_rep)

lemma eshift_end_eset_since:
  "eshift_end args nt (eset_since g i s daux) = eset_since g i s (eshift_end args nt daux)"
  by (cases daux rule: emsaux_cases) (simp add: Let_def split: prod.splits)

lemma eadd_new_ts'_eset_since:
  assumes e: "linearize (eprev_of daux) = []"
  shows "eadd_new_ts_msaux' args nt (eset_since g i s daux)
    = eset_since g i s (eadd_new_ts_msaux' args nt daux)"
proof (cases daux rule: emsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  obtain dp' mv where tdw: "takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) dp = (dp', mv)"
    by (cases "takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) dp")
  have mv: "mv = []"
    using takedropWhile_queue_snd[of "\<lambda>(t, X). memL (args_ivl args) (nt - t)" dp] e
    unfolding 1 tdw by simp
  show ?thesis unfolding 1
    by (simp add: tdw mv Let_def del: takedropWhile_queue.simps)
qed

lemma eprev_of_eshift_end:
  assumes e: "linearize (eprev_of daux) = []"
  shows "linearize (eprev_of (eshift_end args nt daux)) = []"
proof (cases daux rule: emsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  show ?thesis using e unfolding 1
    by (simp add: Let_def dropWhile_queue_rep del: dropWhile_queue.simps takedropWhile_queue.simps
        split: prod.splits)
qed

lemma eprev_of_dadd_new_ts':
  assumes e: "linearize (eprev_of daux) = []"
  shows "linearize (eprev_of (eadd_new_ts_msaux' args nt daux)) = []"
proof (cases daux rule: emsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  obtain dp' mv where tdw: "takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) dp = (dp', mv)"
    by (cases "takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) dp")
  have "linearize dp' = []"
    using takedropWhile_queue_fst[of "\<lambda>(t, X). memL (args_ivl args) (nt - t)" dp] e
    unfolding 1 tdw by (simp add: dropWhile_queue_rep del: dropWhile_queue.simps)
  then show ?thesis unfolding 1
    by (simp add: tdw Let_def del: takedropWhile_queue.simps split: prod.splits)
qed

lemma valid_dadd_new_ts_lz:
  assumes v: "valid_emsaux_lz args msk cur daux ys" and nt: "nt \<ge> cur"
  shows "valid_emsaux_lz args msk nt (eadd_new_ts_msaux args nt daux)
     (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) ys)"
proof (cases "memL (args_ivl args) 0")
  case True
  obtain g i s where vw: "valid_emsaux args msk cur (eset_since g i s daux) ys"
    and dp: "linearize (eprev_of daux) = []"
    using v True unfolding valid_emsaux_lz_def by auto
  have dp': "linearize (eprev_of (eshift_end args nt daux)) = []"
    by (rule eprev_of_eshift_end[OF dp])
  have "eadd_new_ts_msaux args nt (eset_since g i s daux)
      = eset_since g i s (eadd_new_ts_msaux args nt daux)"
    unfolding eadd_new_ts_msaux_def eshift_end_eset_since eadd_new_ts'_eset_since[OF dp'] ..
  then have "valid_emsaux args msk nt (eset_since g i s (eadd_new_ts_msaux args nt daux))
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) ys)"
    using valid_dadd_new_ts[OF vw nt] by simp
  moreover have "linearize (eprev_of (eadd_new_ts_msaux args nt daux)) = []"
    unfolding eadd_new_ts_msaux_def by (rule eprev_of_dadd_new_ts'[OF dp'])
  ultimately show ?thesis unfolding valid_emsaux_lz_def if_P[OF True] by blast
next
  case False
  then show ?thesis using v valid_dadd_new_ts[OF _ nt] by (simp add: valid_emsaux_lz_def)
qed

lemma eadd_new_table_lz_eset_since:
  assumes "memL (args_ivl args) 0"
  shows "\<exists>i' s'. eadd_new_table_msaux args X (eset_since g i s daux)
    = eset_since g i' s' (eadd_new_table_lz args X daux)"
  using assms by (cases daux rule: emsaux_cases) (auto simp: Let_def)

lemma valid_eadd_new_table_lz:
  assumes v: "valid_emsaux_lz args msk cur daux ys" and X: "table (args_R args) X"
  shows "valid_emsaux_lz args msk cur (eadd_new_table_lz args X daux)
    (case ys of [] \<Rightarrow> [(cur, X)]
     | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # ys)"
proof (cases "memL (args_ivl args) 0")
  case True
  obtain g i s where vw: "valid_emsaux args msk cur (eset_since g i s daux) ys"
    and dp: "linearize (eprev_of daux) = []"
    using v True unfolding valid_emsaux_lz_def by auto
  obtain i' s' where e: "eadd_new_table_msaux args X (eset_since g i s daux)
      = eset_since g i' s' (eadd_new_table_lz args X daux)"
    using eadd_new_table_lz_eset_since[OF True] by blast
  have "linearize (eprev_of (eadd_new_table_lz args X daux)) = []"
    using dp True by (cases daux rule: emsaux_cases) simp
  then show ?thesis using valid_dadd_new_table[OF vw X]
    unfolding e valid_emsaux_lz_def if_P[OF True] by blast
next
  case False
  have "eadd_new_table_lz args X daux = eadd_new_table_msaux args X daux"
    using False by (cases daux rule: emsaux_cases) simp
  then show ?thesis using v valid_dadd_new_table[OF _ X] False
    by (simp add: valid_emsaux_lz_def)
qed

lemma ejoin_eset_since:
  "\<exists>i' s'. ejoin_msaux args Y (eset_since g i s daux) = eset_since g i' s' (ejoin_msaux args Y daux)"
proof (cases daux rule: emsaux_cases)
  case (1 t gc msk dp di ti ii tui idxs tus)
  show ?thesis
  proof (cases "\<forall>i \<in> set msk. \<not> i")
    case True
    show ?thesis
      unfolding 1 eset_since.simps ejoin_msaux.simps if_P[OF True] Let_def by simp
  next
    case nA: False
    show ?thesis
    proof (cases "\<forall>i \<in> set msk. i")
      case True
      show ?thesis
        unfolding 1 eset_since.simps ejoin_msaux.simps if_not_P[OF nA] if_P[OF True] Let_def
        by simp
    next
      case False
      show ?thesis
        unfolding 1 eset_since.simps ejoin_msaux.simps if_not_P[OF nA] if_not_P[OF False] Let_def
        by simp
    qed
  qed
qed

lemma egc_eset_since:
  "\<exists>g' i' s'. egc_msaux args (eset_since g i s daux) = eset_since g' i' s' daux"
  by (cases daux rule: emsaux_cases) (auto simp: Let_def)

lemma valid_egc_join_lz:
  assumes v: "valid_emsaux_lz args msk cur daux ys" and dm: "emsk_args args msk"
    and tY: "table (args_L args) Y"
  shows "valid_emsaux_lz args msk cur (egc_join_lz args Y daux)
     (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) Y)) ys)"
proof (cases "memL (args_ivl args) 0")
  case True
  obtain g i s where vw: "valid_emsaux args msk cur (eset_since g i s daux) ys"
    and dp: "linearize (eprev_of daux) = []"
    using v True unfolding valid_emsaux_lz_def by auto
  have gj: "\<exists>g' i' s'. egc_join_msaux args Y (eset_since g i s daux)
      = eset_since g' i' s' (ejoin_msaux args Y daux)"
  proof -
    have alt: "egc_join_msaux args Y (eset_since g i s daux)
        = ejoin_msaux args Y (egc_msaux args (eset_since g i s daux))
      \<or> egc_join_msaux args Y (eset_since g i s daux) = ejoin_msaux args Y (eset_since g i s daux)"
      by (cases daux rule: emsaux_cases) auto
    obtain g1 i1 s1 where c: "egc_msaux args (eset_since g i s daux) = eset_since g1 i1 s1 daux"
      using egc_eset_since by blast
    show ?thesis using alt unfolding c by (metis ejoin_eset_since)
  qed
  then obtain g' i' s' where e: "egc_join_msaux args Y (eset_since g i s daux)
      = eset_since g' i' s' (ejoin_msaux args Y daux)" by blast
  have "linearize (eprev_of (ejoin_msaux args Y daux)) = []"
    using dp by (cases daux rule: emsaux_cases) (simp add: Let_def)
  moreover have "valid_emsaux args msk cur (egc_join_msaux args Y (eset_since g i s daux))
      (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) Y)) ys)"
    by (rule valid_dgc_join[OF vw dm tY])
  ultimately show ?thesis
    unfolding e egc_join_lz_def valid_emsaux_lz_def if_P[OF True] by blast
next
  case False
  then show ?thesis using v valid_dgc_join[OF _ dm tY]
    by (simp add: valid_emsaux_lz_def egc_join_lz_def)
qed

lemma valid_eresult_msaux_lz:
  "valid_emsaux_lz args msk cur daux ys \<Longrightarrow> eresult_msaux args daux
    = foldr (\<union>) [rel. (t, rel) \<leftarrow> ys, memL (args_ivl args) (cur - t)] {}"
  unfolding valid_emsaux_lz_def
  by (cases daux rule: emsaux_cases) (auto dest: valid_eresult_msaux split: if_splits)

lemma eframe_sub:
  "eframe kR cR \<Longrightarrow> eframe kL cL \<Longrightarrow> set kL \<subseteq> set kR \<Longrightarrow> set cL \<subseteq> set cR"
  by (simp add: eframe_def)

lemma esaux'_init:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "esaux' kR cR cL args 0 (einit_msaux (eargs cR cL args) (emsk cR cL)) []"
proof -
  have "valid_emsaux_lz (init_args (args_ivl args) (length cR) cL cR (args_pos args) None)
      (emsk cR cL) 0
      (einit_msaux (init_args (args_ivl args) (length cR) cL cR (args_pos args) None) (emsk cR cL)) []"
    by (rule valid_einit_msaux_lz[OF eframe_sub[OF fR fL sub] eframeD(4)[OF fL] eframeD(4)[OF fR]])
  then show ?thesis by (simp add: esaux'_def eargs_def eauxlist_def)
qed

lemma esaux'_add_new_ts:
  assumes v: "esaux' kR cR cL args cur daux auxlist" and nt: "cur \<le> nt"
  shows "esaux' kR cR cL args nt (eadd_new_ts_msaux (eargs cR cL args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and d: "valid_emsaux_lz (eargs cR cL args) (emsk cR cL) cur daux (eauxlist kR cR auxlist)"
    using v by (auto simp: esaux'_def)
  have "valid_emsaux_lz (eargs cR cL args) (emsk cR cL) nt
      (eadd_new_ts_msaux (eargs cR cL args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl (eargs cR cL args)) (nt - t)) (eauxlist kR cR auxlist))"
    by (rule valid_dadd_new_ts_lz[OF d nt])
  then show ?thesis using w by (simp add: esaux'_def eauxlist_filter)
qed

lemma esaux'_join:
  assumes v: "esaux' kR cR cL args cur daux auxlist"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and t1: "table kL rel1"
  shows "esaux' kR cR cL args cur (egc_join_lz (eargs cR cL args) (etabc kL cL rel1) daux)
      (map (\<lambda>(t, rel). (t, join kR rel (args_pos args) kL rel1)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and d: "valid_emsaux_lz (eargs cR cL args) (emsk cR cL) cur daux (eauxlist kR cR auxlist)"
    using v by (auto simp: esaux'_def)
  have dm: "emsk_args (eargs cR cL args) (emsk cR cL)"
    unfolding emsk_def
    by (rule emsk_args_dargs[OF eframeD(2)[OF fR] eframeD(2)[OF fL] eframe_sub[OF fR fL sub]])
  have tY: "table (args_L (eargs cR cL args)) (etabc kL cL rel1)" by (simp add: table_etabc)
  have "valid_emsaux_lz (eargs cR cL args) (emsk cR cL) cur
      (egc_join_lz (eargs cR cL args) (etabc kL cL rel1) daux)
      (map (\<lambda>(t, rel). (t, join cR rel (args_pos args) cL (etabc kL cL rel1)))
        (eauxlist kR cR auxlist))"
    using valid_egc_join_lz[OF d dm tY] by simp
  then show ?thesis using w
    by (simp add: esaux'_def eauxlist_join[OF fR fL sub w t1] eauxlist_wf_join[OF w sub t1])
qed

lemma esaux'_add_new_table:
  assumes v: "esaux' kR cR cL args cur daux auxlist" and t2: "table kR rel2"
  shows "esaux' kR cR cL args cur (eadd_new_table_lz (eargs cR cL args) (etabc kR cR rel2) daux)
      (case auxlist of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and d: "valid_emsaux_lz (eargs cR cL args) (emsk cR cL) cur daux (eauxlist kR cR auxlist)"
    using v by (auto simp: esaux'_def)
  have tt: "table (args_R (eargs cR cL args)) (etabc kR cR rel2)" by (simp add: table_etabc)
  have "valid_emsaux_lz (eargs cR cL args) (emsk cR cL) cur
      (eadd_new_table_lz (eargs cR cL args) (etabc kR cR rel2) daux)
      (case eauxlist kR cR auxlist of [] \<Rightarrow> [(cur, etabc kR cR rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> etabc kR cR rel2) # r
                         else (cur, etabc kR cR rel2) # eauxlist kR cR auxlist)"
    by (rule valid_eadd_new_table_lz[OF d tt])
  then show ?thesis using w t2
    by (simp add: esaux'_def eauxlist_add_new_table[symmetric] eauxlist_wf_add_new_table[OF w t2])
qed

lemma esaux'_result:
  assumes v: "esaux' kR cR cL args cur daux auxlist"
  shows "eresult_msaux (eargs cR cL args) daux
      = etabc kR cR (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof -
  have d: "valid_emsaux_lz (eargs cR cL args) (emsk cR cL) cur daux (eauxlist kR cR auxlist)"
    using v by (auto simp: esaux'_def)
  have "eresult_msaux (eargs cR cL args) daux
      = foldr (\<union>) [rel. (t, rel) \<leftarrow> eauxlist kR cR auxlist,
          memL (args_ivl (eargs cR cL args)) (cur - t)] {}"
    by (rule valid_eresult_msaux_lz[OF d])
  then show ?thesis by (simp add: etabc_result)
qed

lemma table_unit_table_Nil: "table ks unit_table \<Longrightarrow> ks = []"
  by (simp add: table_def unit_table_def)

lemma etabc_eq_empty_table[simp]: "etabc ks cs T = empty_table \<longleftrightarrow> T = empty_table"
  by (simp add: etabc_empty_iff empty_table_def)

(*<*)
end
(*>*)
