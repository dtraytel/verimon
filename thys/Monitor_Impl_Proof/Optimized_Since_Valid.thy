(*<*)
theory Optimized_Since_Valid
  imports "Monitor_Impl.Optimized_Since" Optimized_Common_Facts
begin
(*>*)

section \<open>Correctness of the optimized Since structure\<close>

subsection \<open>Folds over the tuple mappings\<close>

lemma fold_filter_set_sub: "fold filter_set xs (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> \<Union>(snd ` set xs)"
proof (induction xs arbitrary: m Y)
  case (Cons a xs)
  show ?case
    using Cons(2)
    by (cases a; cases "filter_set a (m, Y)") (auto dest: Cons(1) filter_set_sub)
qed auto

lemma fold_filter_set_Some_None: "Mapping.lookup ts as = Some t \<Longrightarrow>
  as \<in> X \<Longrightarrow> (t, X) \<in> set ds \<Longrightarrow> fold filter_set ds (ts, Y) = (ts', Y') \<Longrightarrow>
  Mapping.lookup ts' as = None \<and> as \<in> Y'"
proof (induction ds arbitrary: ts Y)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    obtain ts'' Y'' where step: "filter_set a (ts, Y) = (ts'', Y'')"
      by fastforce
    show ?thesis
    proof (cases "Mapping.lookup ts'' as")
      case None
      have "as \<in> Y''"
        using Cons(2) None step
        by (auto simp: Pair filter_set.simps Let_def Mapping_keys_intro keys_is_none_rep)
      then have "fold filter_set ds (ts'', Y'') = (ts', Y') \<Longrightarrow> as \<in> Y'"
        by (induction ds arbitrary: ts'' Y'') (auto simp: filter_set.simps Let_def)
      moreover have "fold filter_set ds (ts'', Y'') = (ts', Y') \<Longrightarrow> Mapping.lookup ts' as = None"
        using None Mapping_lookup_filter_not_None
        by (induction ds arbitrary: ts'' Y'') (fastforce simp: filter_set.simps Let_def)+
      ultimately show ?thesis
        using Cons(5)
        by (auto simp: step)
    next
      case (Some t'')
      have lookup_ts'': "Mapping.lookup ts'' as = Some t"
        using Cons(2) step Some Mapping_lookup_filter_not_None
        by (fastforce simp: Pair filter_set.simps Let_def Mapping_lookup_filter_None)
      have set_ds: "(t, X) \<in> set ds"
        using Cons(2,3,4) step Some
        by (auto simp: filter_set.simps Let_def Mapping_lookup_filter_None)
      show ?thesis
        using Cons lookup_ts'' set_ds
        by (auto simp: step)
    qed
  qed
qed simp

lemma fold_filter_set_Some_Some: "Mapping.lookup ts as = Some t \<Longrightarrow>
  (\<And>X. (t, X) \<in> set ds \<Longrightarrow> as \<notin> X) \<Longrightarrow> fold filter_set ds (ts, Y) = (ts', Y') \<Longrightarrow>
  Mapping.lookup ts' as = Some t \<and> (as \<in> Y' \<longleftrightarrow> as \<in> Y)"
proof (induction ds arbitrary: ts Y)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    obtain ts'' Y'' where step: "filter_set a (ts, Y) = (ts'', Y'')"
      by fastforce
    show ?thesis
    proof (cases "Mapping.lookup ts'' as")
      case None
      have ts'': "ts'' = Mapping.filter (filter_cond X' ts t') ts"
        using step by (simp add: Pair filter_set.simps Let_def)
      have "as \<in> X' \<and> Mapping.lookup ts as = Some t'"
      proof (rule ccontr)
        assume "\<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t')"
        then have "Mapping.lookup ts'' as = Mapping.lookup ts as"
          unfolding ts'' by (rule Mapping_lookup_filter_Some)
        with None Cons(2) show False
          by simp
      qed
      with Cons(2) Pair have "(t, X') \<in> set (a # ds)" and "as \<in> X'"
        by simp_all
      with Cons(3) have "False"
        by blast
      then show ?thesis ..
    next
      case (Some t'')
      have lookup_ts'': "Mapping.lookup ts'' as = Some t"
        using Cons(2) step Some Mapping_lookup_filter_not_None
        by (fastforce simp: Pair filter_set.simps Let_def Mapping_lookup_filter_None)
      have "as \<in> Y'' \<longleftrightarrow> as \<in> Y"
        using step Mapping_keys_intro Some
        by (force simp: Pair filter_set.simps Let_def)
      then show ?thesis
        using Cons(1)[OF lookup_ts''] Cons(3,4)
        by (auto simp: step)
    qed
  qed
qed simp

lemma fold_upd_set_keys_sub:
  assumes Z_sub: "\<And>X t. Z X t \<subseteq> X"
  shows "fold (upd_set_keys Z) xs (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> \<Union>(snd ` set xs)"
proof (induction xs arbitrary: m Y)
  case (Cons a xs)
  show ?case
    using Cons(2) Z_sub
    by (cases a; cases "upd_set_keys Z a (m, Y)") (fastforce dest: Cons(1) upd_set_keys_sub)
qed auto

lemma fold_upd_set_keys:
  assumes "fold (upd_set_keys Z) mv (ts, {}) = (ts', Y)"
  shows "ts' = fold (\<lambda>(t, X) ts. upd_set ts (\<lambda>_. t) (Z X t)) mv ts"
    "Mapping.keys ts' = Mapping.keys ts \<union> Y"
proof -
  have fst_fold_upd_set_keys: "fst (fold (upd_set_keys Z) mv (ts, Y0)) = fold (\<lambda>(t, X) ts. upd_set ts (\<lambda>_. t) (Z X t)) mv ts"
    for Y0 :: "'a set"
    by (induction mv arbitrary: ts Y0) (auto simp: upd_set_keys.simps)
  show "ts' = fold (\<lambda>(t, X) ts. upd_set ts (\<lambda>_. t) (Z X t)) mv ts"
    using fst_fold_upd_set_keys[where ?Y0.0="{}"]
    by (auto simp: assms)
  have keys_fold_upd_set_keys: "Y0 \<subseteq> Y \<and> Mapping.keys ts \<subseteq> Mapping.keys ts' \<and> Mapping.keys ts' \<union> Y0 = Mapping.keys ts \<union> Y" if "fold (upd_set_keys Z) mv (ts, Y0) = (ts', Y)" for Y0
    using that
  proof (induction mv arbitrary: ts Y0)
    case (Cons a mv)
    show ?case
    proof (cases a)
      case (Pair t' X')
      let ?ts = "upd_set ts (\<lambda>_. t') (Z X' t')"
      have "fold (upd_set_keys Z) mv (?ts, Y0 \<union> Z X' t') = (ts', Y)"
        using Cons(2) by (simp add: Pair upd_set_keys.simps)
      then have "Y0 \<union> Z X' t' \<subseteq> Y \<and> Mapping.keys ?ts \<subseteq> Mapping.keys ts' \<and>
        Mapping.keys ts' \<union> (Y0 \<union> Z X' t') = Mapping.keys ?ts \<union> Y"
        by (rule Cons(1))
      moreover have "Mapping.keys ?ts = Mapping.keys ts \<union> Z X' t'"
        by (rule Mapping_upd_set_keys)
      ultimately show ?thesis
        by blast
    qed
  qed simp
  show "Mapping.keys ts' = Mapping.keys ts \<union> Y"
    using keys_fold_upd_set_keys[OF assms]
    by auto
qed

subsection \<open>Time-stamped tuples and indexed tables\<close>

lemma ts_tuple_rel_ext_Cons: "tas \<in> ts_tuple_rel_f f {(nt, X)} \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_ext_Cons': "tas \<in> ts_tuple_rel_f f (set tass) \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_dest: "(t, as) \<in> ts_tuple_rel_f f ys \<Longrightarrow> \<exists>X. (t, X) \<in> ys \<and> as \<in> f X"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_ext: "tas \<in> ts_tuple_rel_f f {(nt, X)} \<Longrightarrow>
  \<forall> A B. f A \<union> f B = f (A \<union> B) \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, Y \<union> X) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel_f f {(nt, X)}" "\<forall> A B. f A \<union> f B = f (A \<union> B)"
  then obtain as where tas_def: "tas = (nt, as)" "as \<in> f X"
    by (cases tas) (auto simp add: ts_tuple_rel_f_def)
  then have "as \<in> f (Y \<union> X)"
    using assm(2)
    by auto
  then show "tas \<in> ts_tuple_rel_f f (set ((nt, Y \<union> X) # tass))"
    unfolding tas_def(1)
    by (rule ts_tuple_rel_intro) auto
qed

lemma ts_tuple_rel_ext': "tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass)) \<Longrightarrow>
  \<forall> A B. f A \<union> f B = f (A \<union> B) \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, X \<union> Y) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass))" "\<forall> A B. f A \<union> f B = f (A \<union> B)"
  then have "tas \<in> ts_tuple_rel_f f {(nt, X)} \<union> ts_tuple_rel_f f (set tass)"
    using ts_tuple_rel_Un by force
  then show "tas \<in> ts_tuple_rel_f f (set ((nt, X \<union> Y) # tass))"
  proof
    assume "tas \<in> ts_tuple_rel_f f {(nt, X)}"
    then show ?thesis
      using assm(2)
      by (auto simp: Un_commute dest!: ts_tuple_rel_ext)
  next
    assume "tas \<in> ts_tuple_rel_f f (set tass)"
    then have "tas \<in> ts_tuple_rel_f f (set ((nt, X \<union> Y) # tass))"
      by (rule ts_tuple_rel_ext_Cons')
    then show ?thesis by simp
  qed
qed

lemma safe_max_Some_intro: "x \<in> X \<Longrightarrow> \<exists>y. safe_max X = Some y"
  using safe_max_empty by auto

lemma valid_mmsaux_tuple_in_keys: "valid_mmsaux args cur
  (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) ys \<Longrightarrow>
  Mapping.keys tuple_in = snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
  valid_tuple tuple_since tas}"
  by (auto intro!: Mapping_keys_intro safe_max_Some_intro
      dest!: Mapping.in_keysD safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel]
      simp add: newest_tuple_in_mapping_def)+

lemma distinct_wf_table_sig[simp]: "distinct (wf_table_sig t)"
  by transfer auto

lemma wf_table_set_table: "wf_table_sig t = cs \<Longrightarrow> table cs (wf_table_set t)"
  by transfer auto

lemma distinct_wf_idx_sig[simp]: "distinct (wf_idx_sig t)"
  by transfer auto

lemma wf_table_sig_args: "distinct (args_R args) \<Longrightarrow> wf_table_sig (wf_table_of_set_args args X) = args_R args"
  by (auto simp: wf_table_of_set_args_def wf_idx_sig_of_set)

lemma wf_table_of_set_args: "distinct (args_R args) \<Longrightarrow> table (args_R args) X \<Longrightarrow>
  wf_table_set (wf_table_of_set_args args X) = X"
  by (auto simp: wf_table_of_set_args_def wf_idx_set_of_set table_def)

lemma wf_table_of_set_args_wf_table_set: "wf_table_sig t = args_R args \<Longrightarrow>
  wf_table_of_set_args args (wf_table_set t) = t"
  using distinct_wf_table_sig[of t]
  by (auto simp: wf_table_sig_args wf_table_of_set_args[OF _ wf_table_set_table] intro: wf_table_eqI)

lemma wf_table_sig_of_keys[simp]: "distinct cs \<Longrightarrow> wf_table_sig (wf_table_of_keys cs m) = cs"
  by (simp add: wf_table_of_keys_def wf_table_sig_of_set)

lemma wf_table_set_of_keys: "distinct cs \<Longrightarrow> table cs (Mapping.keys m) \<Longrightarrow>
  wf_table_set (wf_table_of_keys cs m) = Mapping.keys m"
  by (auto simp: wf_table_of_keys_def wf_table_set_of_set table_def)

lemma wf_table_sig_upd: "distinct (args_R args) \<Longrightarrow> wf_table_sig (w ()) = args_R args \<Longrightarrow>
  wf_table_sig (wf_table_upd args m w) = args_R args"
  by (simp add: wf_table_upd_def)

lemma wf_table_set_upd: "distinct (args_R args) \<Longrightarrow> table (args_R args) (Mapping.keys m) \<Longrightarrow>
  wf_table_set (w ()) = Mapping.keys m \<Longrightarrow> wf_table_set (wf_table_upd args m w) = Mapping.keys m"
  by (simp add: wf_table_upd_def wf_table_set_of_keys)

subsection \<open>Initialization and shifting the window\<close>

lemma valid_init_mmsaux: "set L \<subseteq> set R \<Longrightarrow> distinct L \<Longrightarrow> distinct R \<Longrightarrow>
  valid_mmsaux (init_args I n L R b agg) 0 (init_mmsaux (init_args I n L R b agg)) []"
  by (auto simp add: init_args_def empty_queue_rep ts_tuple_rel_f_def
      safe_max_def table_def wf_table_of_set_args_def wf_idx_sig_of_set wf_idx_set_of_set)

lemma valid_shift_end_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args cur (shift_end args nt
    (ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  define I where "I = args_ivl args"
  define data_in' where "data_in' \<equiv>
    fst (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
  define data_prev' where "data_prev' \<equiv>
    dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev"
  define discard where "discard \<equiv>
    snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
  have set_discard: "\<Union>(snd ` set discard) \<subseteq> \<Union>(snd ` (set (linearize data_in)))"
    by (auto simp: discard_def takedropWhile_queue_snd simp del: takedropWhile_queue.simps dest: set_takeWhileD)
  obtain tuple_in' del where fold_filter_set: "fold filter_set discard (tuple_in, {}) = (tuple_in', del)"
    by (cases "fold filter_set discard (tuple_in, {})") auto
  have tuple_in_Some_None: "Mapping.lookup tuple_in' as = None" "as \<in> del"
    if "Mapping.lookup tuple_in as = Some t" "as \<in> X" "(t, X) \<in> set discard" for as t X
    using fold_filter_set_Some_None[OF _ _ _ fold_filter_set] that
    by auto
  have tuple_in_Some_Some: "Mapping.lookup tuple_in' as = Some t" "as \<notin> del"
    if "Mapping.lookup tuple_in as = Some t" "\<And>X. (t, X) \<in> set discard \<Longrightarrow> as \<notin> X" for as t
    using fold_filter_set_Some_Some[OF _ _ fold_filter_set] that
    by auto
  have tuple_in_None: "Mapping.lookup tuple_in' as = None" "as \<notin> del"
    if "Mapping.lookup tuple_in as = None" for as
    using fold_filter_set_None[OF _ fold_filter_set] that
    by auto
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_Some_None tuple_in_Some_Some tuple_in_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping.in_keysD)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    using valid_before nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    using valid_before nt_mono by auto
  have lin_data_in': "linearize data_in' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_in)"
    unfolding data_in'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F1(1)] ..
  then have set_lin_data_in': "set (linearize data_in') \<subseteq> set (linearize data_in)"
    by auto
  have "sorted (map fst (linearize data_in))"
    using valid_before by auto
  then have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using sorted_filter by auto
  have discard_alt: "discard = filter (\<lambda>(t, X). \<not> memR I (nt - t)) (linearize data_in)"
    unfolding discard_def[unfolded takedropWhile_queue_snd] takeWhile_filter[OF F1(1)] ..
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_prev)"
    unfolding data_prev'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F2(1)] ..
  have "sorted (map fst (linearize data_prev))"
    using valid_before by auto
  then have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter by auto
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before by (auto dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using ts_tuple_rel_mono[OF set_lin_data_in'] by auto
      then show ?thesis
        unfolding tuple_in_None[OF None] 
        using iffD2[OF safe_max_empty, symmetric] by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "\<exists>X. (t, X) \<in> set discard \<and> as \<in> X")
        case True
        then obtain X where X_def: "(t, X) \<in> set discard" "as \<in> X"
          by auto
        have "\<not> memR I (nt - t)"
          using X_def(1) unfolding discard_alt by simp
        moreover have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        ultimately have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas} = {}"
          unfolding lin_data_in' using ts_tuple_rel_set_filter
          by (fastforce simp add: ts_tuple_rel_f_def memR_antimono)
        then show ?thesis
          unfolding tuple_in_Some_None[OF Some X_def(2,1)]
          using iffD2[OF safe_max_empty, symmetric] by blast
      next
        case False
        then have lookup_Some: "Mapping.lookup tuple_in' as = Some t"
          using tuple_in_Some_Some[OF Some] by auto
        have t_as: "(t, as) \<in> ts_tuple_rel (set (linearize data_in))"
          "valid_tuple tuple_since (t, as)"
          using valid_before Some by (auto dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then obtain X where X_def: "as \<in> X" "(t, X) \<in> set (linearize data_in)"
          by (auto simp add: ts_tuple_rel_f_def)
        have "(t, X) \<in> set (linearize data_in')"
          using X_def False unfolding discard_alt lin_data_in' by auto
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}"
          using t_as(2) X_def(1) by (auto simp add: ts_tuple_rel_f_def image_iff)
        have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel, OF _ t_in_fst]
            ts_tuple_rel_mono[OF set_lin_data_in'] by fastforce
        then show ?thesis
          unfolding lookup_Some using t_in_fst by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_in: "table (args_R args) (Mapping.keys tuple_in)"
    and table_in': "table (args_R args) (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before by (auto simp add: table_def)
  have keys_tuple_in: "table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  then have keys_tuple_in': "table_in - del = Mapping.keys tuple_in'"
    using tuple_in_None tuple_in'_keys tuple_in_Some_Some tuple_in_Some_None
    by auto (metis Mapping.in_keysD Mapping_keys_intro option.distinct(1))+
  have sig_in: "wf_table_sig wf_table_in = args_R args"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have sig_in'': "wf_table_sig (wf_table_upd args tuple_in' (\<lambda>_. wf_table_antijoin wf_table_in (wf_table_of_set_args args del))) = args_R args"
    and sig_since: "wf_table_sig wf_table_since = args_R args"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto intro!: wf_table_sig_upd simp: wf_table_sig_antijoin)
  have distR: "distinct (args_R args)"
    using valid_before by auto
  have "table (args_R args) (\<Union>(snd ` (set (linearize data_in))))"
    using valid_before
    by (auto simp: table_def)
  then have table_del: "table (args_R args) del"
    using fold_filter_set_sub[OF fold_filter_set] set_discard table_subset
    by fastforce
  have keys_tuple_in'': "wf_table_set (wf_table_upd args tuple_in' (\<lambda>_. wf_table_antijoin wf_table_in (wf_table_of_set_args args del))) = Mapping.keys tuple_in'"
    by (rule wf_table_set_upd[OF distR table_in'])
      (simp add: keys_tuple_in keys_tuple_in'[symmetric] set_in[symmetric]
        wf_table_set_antijoin sig_in wf_table_sig_args[OF distR] wf_table_of_set_args[OF distR table_del]
        join_eq[OF table_del wf_table_set_table[OF sig_in] distR])
  have "ts_tuple_rel (set auxlist) =
    {as \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since as}"
    using valid_before by auto
  then have "ts_tuple_rel (set (filter (\<lambda>(t, rel). memR I (nt - t)) auxlist)) =
    {as \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since as}"
    unfolding lin_data_prev' lin_data_in' ts_tuple_rel_Un ts_tuple_rel_filter by auto
  then show ?thesis
    using data_prev'_def data_in'_def fold_filter_set discard_def valid_before nt_mono
      sorted_lin_data_prev' sorted_lin_data_in' lin_data_prev' lin_data_in' lookup_tuple_in'
      table_in' keys_tuple_in' sig_in'' keys_tuple_in'' sig_since keys_since unfolding I_def
    unfolding valid_mmsaux.simps shift_end.simps Let_def split_beta
    by auto
qed

lemma valid_shift_end_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args cur (shift_end args nt aux)
  (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_shift_end_mmsaux_unfolded by (cases aux) fast

subsection \<open>Adding a new time stamp\<close>

lemma Mapping_lookup_fold_upd_set_max: "{(t, X) \<in> set xs. as \<in> Z X t} \<noteq> {} \<Longrightarrow>
  sorted (map fst xs) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as =
  Some (Max (fst ` {(t, X) \<in> set xs. as \<in> Z X t}))"
proof (induction xs arbitrary: m)
  case (Cons x xs)
  obtain t X where tX_def: "x = (t, X)"
    by (cases x) auto
  have set_fst_eq: "(fst ` {(t, X). (t, X) \<in> set (x # xs) \<and> as \<in> Z X t}) =
    ((fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t}) \<union>
    (if as \<in> Z X t then {t} else {}))"
    using image_iff by (fastforce simp add: tX_def split: if_splits)
  show ?case
  proof (cases "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<noteq> {}")
    case True
    have "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<subseteq> set xs"
      by auto
    then have fin: "finite (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      by (simp add: finite_subset)
    have "Max (insert t (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})) =
      Max (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      using Max_Un_absorb[OF fin, of "{t}"] True Cons(3) tX_def by auto
    then show ?thesis
      using Cons True unfolding set_fst_eq by auto
  next
    case False
    then have empty: "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} = {}"
      by auto
    then have "as \<in> Z X t"
      using Cons(2) set_fst_eq by fastforce
    then show ?thesis
      using Mapping_lookup_fold_upd_set_idle[OF empty] unfolding set_fst_eq empty
      by (auto simp add: Mapping_lookup_upd_set tX_def)
  qed
qed simp

lemma valid_add_new_ts_mmsaux'_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux' args nt
    (ot, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)) auxlist"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define data_prev' where "data_prev' \<equiv> dropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev"
  define move where "move \<equiv> takeWhile (\<lambda>(t, X). memL I (nt - t)) (linearize data_prev)"
  define data_in' where "data_in' \<equiv> fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in)
    move data_in"
  obtain tuple_in' add where aux:
    "fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)})) move (tuple_in, {}) = (tuple_in', add)"
    by fastforce
  note tuple_in'_def = fold_upd_set_keys(1)[OF aux]
  note add_def = fold_upd_set_keys(2)[OF aux]
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in \<or>
    (\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)})"
    using Mapping_keys_fold_upd_set[of _ "\<lambda>t X. {as \<in> X. valid_tuple tuple_since (t, as)}"]
    by (auto simp add: tuple_in'_def)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_in). t \<le> ot \<and> memL I (ot - t)"
    using valid_before nt_mono unfolding I_def by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> ot \<and> \<not> memL I (ot - t)"
    using valid_before nt_mono unfolding I_def by auto
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). \<not> memL I (nt - t)) (linearize data_prev)"
    unfolding data_prev'_def dropWhile_queue_rep dropWhile_filter'[OF F2(1)] ..
  have move_filter: "move = filter (\<lambda>(t, X). memL I (nt - t)) (linearize data_prev)"
    unfolding move_def takeWhile_filter'[OF F2(1)] ..
  then have sorted_move: "sorted (map fst move)"
    using sorted_filter F2 by auto
  have "\<forall>t\<in>fst ` set move. t \<le> ot \<and> \<not> memL I (ot - t)"
    using move_filter F2(3) set_filter by auto
  then have fst_set_before: "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set move. t \<le> t'"
    using F1(3) by (meson le_diff_iff' memL_mono nat_le_linear)
  then have fst_ts_tuple_rel_before: "\<forall>t\<in>fst ` ts_tuple_rel (set (linearize data_in)).
    \<forall>t'\<in>fst ` ts_tuple_rel (set move). t \<le> t'"
    by (fastforce simp add: ts_tuple_rel_f_def)
  have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter F2 by auto
  have lin_data_in': "linearize data_in' = linearize data_in @ move"
    unfolding data_in'_def using fold_append_queue_rep by fastforce
  have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using F1(1) sorted_move fst_set_before by (simp add: sorted_append)
  have set_lin_prev'_in': "set (linearize data_prev') \<union> set (linearize data_in') =
    set (linearize data_prev) \<union> set (linearize data_in)"
    using lin_data_prev' lin_data_in' move_filter by auto
  have ts_tuple_rel': "ts_tuple_rel (set auxlist) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since tas}"
    unfolding set_lin_prev'_in' using valid_before by auto
  have lookup': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')).
    valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "{(t, X) \<in> set move. as \<in> X \<and> valid_tuple tuple_since (t, as)} = {}")
      case True
      have move_absorb: "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        {tas \<in> ts_tuple_rel (set (linearize data_in @ move)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        using True by (auto simp add: ts_tuple_rel_f_def)
      have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        using valid_before by auto
      then have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding lin_data_in' move_absorb .
      then show ?thesis
        using Mapping_lookup_fold_upd_set_idle[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}"] True
        unfolding tuple_in'_def by auto
    next
      case False
      have split: "fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas} \<union>
        fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        unfolding lin_data_in' set_append ts_tuple_rel_Un by auto
      have max_eq: "Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}) =
        Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding split using False fst_ts_tuple_rel_before
        by (fastforce simp add: ts_tuple_rel_f_def
            intro!: Max_Un_absorb[OF finite_fst_ts_tuple_rel _ finite_fst_ts_tuple_rel, symmetric])
      have "fst ` {(t, X). (t, X) \<in> set move \<and> as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas}"
        by (auto simp add: ts_tuple_rel_f_def image_iff)
      then have "Mapping.lookup tuple_in' as = Some (Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}))"
        using Mapping_lookup_fold_upd_set_max[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}", OF _ sorted_move] False
        unfolding tuple_in'_def by (auto simp add: ts_tuple_rel_f_def)
      then show ?thesis
        unfolding max_eq using False
        by (auto simp add: safe_max_def lin_data_in' ts_tuple_rel_f_def)
    qed
  qed
  have table_in': "table R (Mapping.keys tuple_in')"
  proof -
    {
      fix as
      assume assm: "as \<in> Mapping.keys tuple_in'"
      have "wf_tuple R as"
        using tuple_in'_keys[OF assm]
      proof (rule disjE)
        assume "as \<in> Mapping.keys tuple_in"
        then show "wf_tuple R as"
          using valid_before by (auto simp add: table_def n_def R_def)
      next
        assume "\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}"
        then obtain t X where tX_def: "(t, X) \<in> set move" "as \<in> X"
          by auto
        then have "as \<in> \<Union>(snd ` set (linearize data_prev))"
          unfolding move_def using set_takeWhileD by force
        then show "wf_tuple R as"
          using valid_before by (auto simp add: n_def R_def)
      qed
    }
    then show ?thesis
      by (auto simp add: table_def)
  qed
  have table_in: "table (args_R args) (Mapping.keys tuple_in)"
    using valid_before by (auto simp add: table_def)
  have keys_tuple_in: "table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  note keys_tuple_in' = add_def[symmetric]
  have distR: "distinct (args_R args)"
    using valid_before by auto
  have sig_in: "wf_table_sig wf_table_in = args_R args"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have sig_in'': "wf_table_sig (wf_table_upd args tuple_in' (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args add))) = args_R args"
    and sig_since: "wf_table_sig wf_table_since = args_R args"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto intro!: wf_table_sig_upd simp: wf_table_sig_union wf_table_sig_args)
  have "table (args_R args) (\<Union>(snd ` (set (linearize data_prev))))"
    using valid_before
    by (auto simp: table_def)
  moreover have "\<Union> (snd ` set move) \<subseteq> \<Union> (snd ` set (linearize data_prev))"
    by (auto simp: move_filter)
  ultimately have table_add: "table (args_R args) add"
    using fold_upd_set_keys_sub[OF _ aux] table_subset
    by fastforce
  have keys_tuple_in'': "wf_table_set (wf_table_upd args tuple_in' (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args add))) = Mapping.keys tuple_in'"
    by (rule wf_table_set_upd[OF distR table_in'[unfolded n_def R_def]])
      (auto simp: keys_tuple_in keys_tuple_in'[symmetric] set_in[symmetric]
        wf_table_set_union sig_in wf_table_sig_args[OF distR] wf_table_of_set_args[OF distR table_add])
  have data_prev'_move: "(data_prev', move) =
    takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev"
    using takedropWhile_queue_fst takedropWhile_queue_snd data_prev'_def move_def
    by (metis surjective_pairing)
  moreover have "valid_mmsaux args nt (nt, gc, data_prev', data_in', table_in \<union> add,
    wf_table_upd args tuple_in' (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args add)), tuple_in', wf_table_since, tuple_since) auxlist"
    using lin_data_prev' sorted_lin_data_prev' lin_data_in' move_filter sorted_lin_data_in'
      nt_mono valid_before ts_tuple_rel' lookup' memL_mono[of "args_ivl args" "ot - a" "nt - a" for a]
      table_in' keys_tuple_in' sig_in'' keys_tuple_in'' sig_since keys_since unfolding I_def
    unfolding valid_mmsaux.simps Let_def n_def R_def
    by (auto split: option.splits)
  ultimately show ?thesis
    by (auto simp only: add_new_ts_mmsaux'.simps Let_def data_in'_def aux tuple_in'_def I_def
        split: prod.splits)
qed


lemma valid_add_new_ts_mmsaux': "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args nt (add_new_ts_mmsaux' args nt aux) auxlist"
  using valid_add_new_ts_mmsaux'_unfolded by (cases aux) fast

lemma valid_add_new_ts_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_add_new_ts_mmsaux'[OF valid_shift_end_mmsaux[OF assms] assms(2)]
  unfolding add_new_ts_mmsaux_def .

subsection \<open>Join with the left operand\<close>

lemma join_mmsaux_abs_eq:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and table_left: "table (args_L args) X"
  shows "join_mmsaux args X (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    join_mmsaux_abs args X (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
proof -
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  have L_R: "set (args_L args) \<subseteq> set (args_R args)"
    and distL: "distinct (args_L args)" and distR: "distinct (args_R args)"
    using valid_before
    by auto
  have table_in_def: "Mapping.keys tuple_in = table_in"
    and table_table_in: "table (args_R args) table_in"
    and table_tuple_since: "table (args_R args) (Mapping.keys tuple_since)"
    using valid_before
    by auto
  have sig_in: "wf_table_sig wf_table_in = args_R args"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    and set_args_in: "wf_table_set (wf_table_of_set_args args table_in) = table_in"
    using wf_table_of_set_args valid_before
    by auto
  have sig_since: "wf_table_sig wf_table_since = args_R args"
    and set_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    and set_args_since: "wf_table_set (wf_table_of_set_args args (Mapping.keys tuple_since)) = Mapping.keys tuple_since"
    using wf_table_of_set_args valid_before
    by auto
  show ?thesis
  proof (cases "args_L args = []")
    case True
    have filter: "Mapping.filter (\<lambda>as _. join_cond pos X (restrict (args_L args) (args_R args) as)) m =
      (if (pos \<longleftrightarrow> [] \<in> X) then m else Mapping.empty)" for m :: "('a tuple, ts) mapping"
      using True by (auto intro!: mapping_eqI simp: Mapping.lookup_filter split: option.splits)
    show ?thesis
      using True
      by (auto simp: Let_def pos_def[symmetric] filter table_in_def wf_table_sig_args[OF distR]
          sig_in set_in set_args_in sig_since set_since set_args_since intro!: wf_table_eqI)
  next
    case False
    show ?thesis
    proof (cases "args_L args = args_R args")
      case eq: True
      define in_del where "in_del = (if pos then table_in - X else table_in \<inter> X)"
      define tuple_in' where "tuple_in' = mapping_delete_set tuple_in in_del"
      define table_in' where "table_in' = table_in - in_del"
      define tuple_since' where "tuple_since' = Mapping.filter (\<lambda>as _. join_cond pos X as) tuple_since"
      have idle_in: "restrict (args_L args) (args_R args) as = as" if "as \<in> Mapping.keys tuple_in" for as
        using that table_table_in restrict_idle[OF distR] by (auto simp: eq table_in_def table_def)
      have idle_since: "restrict (args_L args) (args_R args) as = as" if "as \<in> Mapping.keys tuple_since" for as
        using that table_tuple_since restrict_idle[OF distR] by (auto simp: eq table_def)
      have table_in': "Mapping.keys tuple_in' = table_in'"
        unfolding tuple_in'_def table_in'_def table_in_def[symmetric] by auto
      have table_table_in': "table (args_R args) table_in'"
        using table_table_in by (auto simp: table_in'_def table_def)
      have upd_in: "wf_table_upd args tuple_in' (\<lambda>_. wf_table_of_set_args args table_in') = wf_table_of_set_args args table_in'"
        unfolding wf_table_upd_def using eq
        by (auto intro!: wf_table_eqI simp: wf_table_sig_args[OF distR] wf_table_of_set_args[OF distR table_table_in']
            wf_table_set_of_keys[OF distR table_table_in'[folded table_in']] table_in' distR)
      have tuple_in': "Mapping.filter (\<lambda>as _. join_cond pos X (restrict (args_L args) (args_R args) as)) tuple_in = tuple_in'"
        unfolding tuple_in'_def
        by (cases pos) (auto simp: mapping_delete_set_def in_del_def table_in_def[symmetric] idle_in
            intro!: Mapping_filter_cong)
      have table_tuple_since': "table (args_R args) (Mapping.keys tuple_since')"
        using table_tuple_since by (auto simp: tuple_since'_def table_def Mapping_keys_filter)
      have upd_since: "wf_table_upd args tuple_since' (\<lambda>_. wf_table_of_set_args args (Mapping.keys tuple_since')) =
        wf_table_of_set_args args (Mapping.keys tuple_since')"
        unfolding wf_table_upd_def using eq
        by (auto intro!: wf_table_eqI simp: wf_table_sig_args[OF distR] wf_table_of_set_args[OF distR table_tuple_since']
            wf_table_set_of_keys[OF distR table_tuple_since'] distR)
      have tuple_since': "Mapping.filter (\<lambda>as _. join_cond pos X (restrict (args_L args) (args_R args) as)) tuple_since = tuple_since'"
        unfolding tuple_since'_def
        by (intro Mapping_filter_cong) (simp add: idle_since)
      show ?thesis
        by (simp only: join_mmsaux.simps join_mmsaux_abs.simps Let_def pos_def[symmetric] if_not_P[OF False] if_P[OF eq]
            in_del_def[symmetric] tuple_in'_def[symmetric] table_in'_def[symmetric]
            tuple_since'_def[symmetric] tuple_in' tuple_since' table_in' upd_in upd_since)
    next
      case neq: False
    define wf_X where "wf_X = wf_table_of_idx (wf_idx_of_set (args_L args) (args_L args) X)"
    define wf_in_del where "wf_in_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_in wf_X"
    define in_del where "in_del = wf_table_set wf_in_del"
    define tuple_in' where "tuple_in' = mapping_delete_set tuple_in in_del"
    define table_in' where "table_in' = table_in - in_del"
    define wf_table_in' where "wf_table_in' = wf_table_antijoin wf_table_in wf_in_del"
    define wf_since_del where "wf_since_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_since wf_X"
    define since_del where "since_del = wf_table_set wf_since_del"
    define tuple_since' where "tuple_since' = mapping_delete_set tuple_since since_del"
    define wf_table_since' where "wf_table_since' = wf_table_antijoin wf_table_since wf_since_del"
    note join_sub_R = join_sub[OF distR distL _ table_left L_R]
    have wf_in_set: "wf_table_set wf_table_in = table_in"
      by (auto simp: set_in table_in_def)
    have wf_X_sig: "wf_table_sig wf_X = args_L args"
      by (auto simp: wf_X_def wf_idx_sig_of_set[OF distL])
    have wf_X_set: "wf_table_set wf_X = X"
      using table_left
      by (auto simp: wf_X_def wf_idx_set_of_set[OF distL] table_def)
    have wf_in_del_sig: "wf_table_sig wf_in_del = args_R args"
      using L_R
      by (auto simp: wf_in_del_def wf_table_sig_join wf_table_sig_antijoin sig_in wf_X_sig cols_union_subset)
    have in_del_set: "in_del = join (args_R args) table_in (\<not>pos) (args_L args) X"
      using L_R
      by (auto simp: in_del_def wf_in_del_def wf_table_set_antijoin wf_table_set_join sig_in wf_X_sig
          wf_in_set wf_X_set)
    have table_in': "Mapping.keys tuple_in' = table_in'"
      using keys_filter
      unfolding tuple_in'_def table_in'_def table_in_def[symmetric]
      by auto
    have wf_in'_sig: "wf_table_sig wf_table_in' = args_R args"
      by (auto simp: wf_table_in'_def wf_table_sig_antijoin sig_in)
    have wf_in'_set: "wf_table_set wf_table_in' = table_in'"
      unfolding wf_table_in'_def table_in'_def
      by (simp add: wf_table_set_antijoin sig_in wf_in_del_sig wf_in_set in_del_def[symmetric]
          join_eq[OF wf_table_set_table[OF wf_in_del_sig, folded in_del_def] table_table_in distR])
    have tuple_in': "Mapping.filter (\<lambda>as _. join_cond pos X (restrict (args_L args) (args_R args) as)) tuple_in = tuple_in'"
      unfolding tuple_in'_def
      by (cases pos) (auto simp: mapping_delete_set_def in_del_set table_in_def[symmetric]
          join_sub_R[OF table_table_in[folded table_in_def]] intro!: Mapping_filter_cong)
    have wf_since_del_sig: "wf_table_sig wf_since_del = args_R args"
      using L_R
      by (auto simp: wf_since_del_def wf_table_sig_join wf_table_sig_antijoin sig_since wf_X_sig cols_union_subset)
    have since_del_set: "since_del = join (args_R args) (Mapping.keys tuple_since) (\<not>pos) (args_L args) X"
      using L_R
      by (auto simp: since_del_def wf_since_del_def wf_table_set_antijoin wf_table_set_join sig_since wf_X_sig
          set_since wf_X_set)
    have wf_since'_sig: "wf_table_sig wf_table_since' = args_R args"
      by (auto simp: wf_table_since'_def wf_table_sig_antijoin sig_since)
    have wf_since'_set: "wf_table_set wf_table_since' = Mapping.keys tuple_since'"
      unfolding wf_table_since'_def tuple_since'_def
      by (simp add: wf_table_set_antijoin sig_since wf_since_del_sig set_since since_del_def[symmetric]
          join_eq[OF wf_table_set_table[OF wf_since_del_sig, folded since_del_def] table_tuple_since distR])
    have tuple_since': "Mapping.filter (\<lambda>as _. join_cond pos X (restrict (args_L args) (args_R args) as)) tuple_since = tuple_since'"
      unfolding tuple_since'_def
      by (cases pos) (auto simp: mapping_delete_set_def since_del_set
          join_sub_R[OF table_tuple_since] intro!: Mapping_filter_cong)
    show ?thesis
      using False neq
      by (auto simp only:join_mmsaux.simps join_mmsaux_abs.simps Let_def pos_def[symmetric] wf_X_def[symmetric]
          wf_in_del_def[symmetric] in_del_def[symmetric] tuple_in'_def[symmetric] table_in'_def[symmetric] wf_table_in'_def[symmetric]
          wf_since_del_def[symmetric] since_del_def[symmetric] tuple_since'_def[symmetric] wf_table_since'_def[symmetric]
          table_in' wf_in'_set[symmetric] wf_table_of_set_args_wf_table_set[OF wf_in'_sig] tuple_in'
          wf_since'_set[symmetric] wf_table_of_set_args_wf_table_set[OF wf_since'_sig] tuple_since' split: if_splits)
    qed
  qed
qed
lemma valid_join_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and table_left': "table (args_L args) X"
  shows "valid_mmsaux args cur
    (join_mmsaux args X (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) X)) auxlist)"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  note table_left = table_left'[unfolded n_def[symmetric] L_def[symmetric]]
  have L_R: "set L \<subseteq> set R" and distL: "distinct L" and distR: "distinct R"
    using valid_before by (auto simp: L_def R_def)
  define tuple_in' where "tuple_in' \<equiv>
    Mapping.filter (\<lambda>as _. join_cond pos X (restrict (args_L args) (args_R args) as)) tuple_in"
  define tuple_since' where "tuple_since' \<equiv>
    Mapping.filter (\<lambda>as _. join_cond pos X (restrict (args_L args) (args_R args) as)) tuple_since"
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    unfolding tuple_in'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping.in_keysD)
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping.in_keysD)
  have ts_tuple_rel': "ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join R rel pos L X)) auxlist)) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join R rel pos L X)) auxlist))"
    then obtain t as Z where tas_def: "tas = (t, as)" "as \<in> join R Z pos L X" "(t, Z) \<in> set auxlist"
      "(t, join R Z pos L X) \<in> set (map (\<lambda>(t, rel). (t, join R rel pos L X)) auxlist)"
      by (fastforce simp add: ts_tuple_rel_f_def)
    from tas_def(3) have table_Z: "table R Z"
      using valid_before by (auto simp add: n_def R_def)
    have proj: "as \<in> Z" "join_cond pos X (restrict (args_L args) (args_R args) as)"
      using tas_def(2) join_sub[OF distR distL table_Z table_left L_R]
      by (auto simp add: L_def R_def)
    then have "(t, as) \<in> ts_tuple_rel (set (auxlist))"
      using tas_def(3) by (auto simp add: ts_tuple_rel_f_def)
    then have tas_in: "(t, as) \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in))" "valid_tuple tuple_since (t, as)"
      using valid_before by auto
    then obtain t' where t'_def: "Mapping.lookup tuple_since as = Some t'" "t \<ge> t'"
      by (auto simp add: valid_tuple_def split: option.splits)
    then have valid_tuple_since': "valid_tuple tuple_since' (t, as)"
      using proj(2)
      by (auto simp add: tuple_since'_def Mapping_lookup_filter_Some valid_tuple_def)
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
      valid_tuple tuple_since' tas}"
      using tas_in valid_tuple_since' unfolding tas_def(1)[symmetric] by auto
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in)). valid_tuple tuple_since' tas}"
    then obtain t as where tas_def: "tas = (t, as)" "valid_tuple tuple_since' (t, as)"
      by (auto simp add: ts_tuple_rel_f_def)
    from tas_def(2) have "valid_tuple tuple_since (t, as)"
      unfolding tuple_since'_def using Mapping_lookup_filter_not_None
      by (force simp add: valid_tuple_def split: option.splits)
    then have "(t, as) \<in> ts_tuple_rel (set auxlist)"
      using valid_before assm tas_def(1) by auto
    then obtain Z where Z_def: "as \<in> Z" "(t, Z) \<in> set auxlist"
      by (auto simp add: ts_tuple_rel_f_def)
    then have table_Z: "table R Z"
      using valid_before by (auto simp add: n_def R_def)
    from tas_def(2) have "join_cond pos X (restrict (args_L args) (args_R args) as)"
      unfolding tuple_since'_def using Mapping_lookup_filter_Some_P
      by (fastforce simp add: valid_tuple_def split: option.splits)
    then have as_in_join: "as \<in> join R Z pos L X"
      using join_sub[OF distR distL table_Z table_left L_R] Z_def(1)
      by (auto simp add: L_def R_def)
    then show "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join R rel pos L X)) auxlist))"
      using Z_def unfolding tas_def(1) by (auto simp add: ts_tuple_rel_f_def)
  qed
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before
        by (auto simp add: newest_tuple_in_mapping_def dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas} = {}"
        using Mapping_lookup_filter_not_None
        by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric]
        by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "join_cond pos X (restrict (args_L args) (args_R args) as)")
        case True
        then have lookup_tuple_in': "Mapping.lookup tuple_in' as = Some t"
          using Some unfolding tuple_in'_def by (simp add: Mapping_lookup_filter_Some)
        have "(t, as) \<in> ts_tuple_rel (set (linearize data_in))" "valid_tuple tuple_since (t, as)"
          using valid_before Some
          by (auto simp add: newest_tuple_in_mapping_def dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using True by (auto simp add: image_iff valid_tuple_def tuple_since'_def
            Mapping_lookup_filter_Some split: option.splits)
        have "\<And>t'. valid_tuple tuple_since' (t', as) \<Longrightarrow> valid_tuple tuple_since (t', as)"
          using Mapping_lookup_filter_not_None
          by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
        then have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since' (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff newest_tuple_in_mapping_def)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of _ "linearize data_in"],
            OF _ t_in_fst] by fastforce
        then show ?thesis
          unfolding lookup_tuple_in' using t_in_fst by (auto simp add: safe_max_def)
      next
        case False
        then have lookup_tuple': "Mapping.lookup tuple_in' as = None"
          "Mapping.lookup tuple_since' as = None"
          unfolding tuple_in'_def tuple_since'_def
          by (auto simp add: Mapping_lookup_filter_None)
        then have "\<And>tas. \<not>(valid_tuple tuple_since' tas \<and> as = snd tas)"
          by (auto simp add: valid_tuple_def split: option.splits)
        then show ?thesis
          unfolding lookup_tuple' by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_join': "\<And>t ys. (t, ys) \<in> set auxlist \<Longrightarrow> table R (join R ys pos L X)"
  proof -
    fix t ys
    assume "(t, ys) \<in> set auxlist"
    then have table_ys: "table R ys"
      using valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    show "table R (join R ys pos L X)"
      by (rule join_table[OF table_ys table_left]) (use L_R in \<open>auto simp: cols_union_subset\<close>)
  qed
  have table_in': "table R (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  have table_since': "table R (Mapping.keys tuple_since')"
    using tuple_since'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  show ?thesis
    unfolding join_mmsaux_abs_eq[OF valid_before table_left']
    using valid_before ts_tuple_rel' lookup_tuple_in' tuple_in'_def tuple_since'_def table_join'
      Mapping_filter_keys[of tuple_since "\<lambda>as. case as of Some t \<Rightarrow> t \<le> nt"]
      table_in' wf_table_of_set_args[OF distR[unfolded R_def] table_in'[unfolded R_def]]
      table_since' wf_table_of_set_args[OF distR[unfolded R_def] table_since'[unfolded R_def]]
    by (auto simp add: n_def L_def R_def pos_def table_def Let_def wf_table_sig_args)
qed

lemma valid_join_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  table (args_L args) X \<Longrightarrow> valid_mmsaux args cur
  (join_mmsaux args X aux) (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) X)) auxlist)"
  using valid_join_mmsaux_unfolded by (cases aux) fast

subsection \<open>Garbage collection\<close>

lemma valid_gc_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur (nt, gc, data_prev, data_in,
    table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) ys"
  shows "valid_mmsaux args cur (gc_mmsaux args (nt, gc, data_prev, data_in,
    table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)) ys"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define all_tuples where "all_tuples \<equiv> \<Union>(snd ` (set (linearize data_prev) \<union>
    set (linearize data_in)))"
  define tuple_since' where "tuple_since' \<equiv> Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since"
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping.in_keysD)
  then have table_since': "table R (Mapping.keys tuple_since')"
    using valid_before by (auto simp add: table_def n_def R_def)
  have distR: "distinct (args_R args)"
    using valid_before by auto
  have sig_since'': "wf_table_sig (wf_table_upd args tuple_since' (\<lambda>_. wf_table_of_set_args args (Mapping.keys tuple_since'))) = args_R args"
    by (auto intro!: wf_table_sig_upd simp: wf_table_sig_args distR)
  have keys_since'': "wf_table_set (wf_table_upd args tuple_since' (\<lambda>_. wf_table_of_set_args args (Mapping.keys tuple_since'))) = Mapping.keys tuple_since'"
    by (rule wf_table_set_upd[OF distR table_since'[unfolded n_def R_def]])
      (auto simp: wf_table_of_set_args[OF distR table_since'[unfolded n_def R_def]])
  have data_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in)) \<Longrightarrow> valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
  proof -
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in))"
    define t where "t \<equiv> fst tas"
    define as where "as \<equiv> snd tas"
    have "as \<in> all_tuples"
      using assm by (force simp add: as_def all_tuples_def ts_tuple_rel_f_def)
    then have "Mapping.lookup tuple_since' as = Mapping.lookup tuple_since as"
      by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits)
    then show "valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
      by (auto simp add: valid_tuple_def as_def split: option.splits) metis
  qed
  then have data_in_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
    valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
    by (auto simp add: ts_tuple_rel_Un)
  have "ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
    using data_cong valid_before by auto
  moreover have "(\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas}))"
    using valid_before by (auto simp add: newest_tuple_in_mapping_def) (meson data_in_cong)
  moreover have "(\<forall>as \<in> Mapping.keys tuple_since'. case Mapping.lookup tuple_since' as of
    Some t \<Rightarrow> t \<le> nt)"
    using Mapping.keys_filter valid_before
    by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits
        intro!: Mapping_keys_intro dest: Mapping.in_keysD)
  ultimately show ?thesis
    using valid_before table_since' sig_since'' keys_since''
    unfolding gc_mmsaux.simps Let_def all_tuples_def[symmetric] tuple_since'_def[symmetric] valid_mmsaux.simps
    by (auto simp: n_def R_def)
qed

lemma valid_gc_mmsaux: "valid_mmsaux args cur aux ys \<Longrightarrow> valid_mmsaux args cur (gc_mmsaux args aux) ys"
  using valid_gc_mmsaux_unfolded by (cases aux) fast

lemma gc_join_mmsaux_alt: "gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 (gc_mmsaux args aux) \<or>
  gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 aux"
  by (cases aux) (auto simp only: gc_join_mmsaux.simps split: if_splits)

lemma valid_gc_join_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "table (args_L args) rel1"
  shows "valid_mmsaux args cur (gc_join_mmsaux args rel1 aux)
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist)"
  using gc_join_mmsaux_alt[of args rel1 aux]
  using valid_join_mmsaux[OF valid_gc_mmsaux[OF assms(1)] assms(2)]
    valid_join_mmsaux[OF assms]
  by auto

subsection \<open>Adding a new table\<close>

lemma valid_add_new_table_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and table_X: "table (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X
    (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
proof -
  have cur_nt: "cur = nt"
    using valid_before by auto
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define tuple_in' where "tuple_in' \<equiv> upd_set tuple_in (\<lambda>_. nt) X"
  define X' where "X' \<equiv> X - Mapping.keys tuple_since"
  define tuple_since' where "tuple_since' \<equiv> upd_set tuple_since (\<lambda>_. nt) X'"
  define wf_table_since' where "wf_table_since' \<equiv> wf_table_upd args tuple_since' (\<lambda>_. wf_table_union wf_table_since (wf_table_of_set_args args X'))"
  define data_prev' where "data_prev' \<equiv> append_queue (nt, X) data_prev"
  define data_in' where "data_in' \<equiv> append_queue (nt, X) data_in"
  define auxlist' where "auxlist' \<equiv> (case auxlist of
    [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  have table_in': "table R (Mapping.keys tuple_in')"
    using table_X valid_before
    by (auto simp add: table_def tuple_in'_def Mapping_upd_set_keys n_def R_def)
  have table_since': "table R (Mapping.keys tuple_since')"
    using table_X valid_before
    by (auto simp add: table_def tuple_since'_def Mapping_upd_set_keys n_def R_def X'_def)
  have tuple_since'_keys: "Mapping.keys tuple_since \<subseteq> Mapping.keys tuple_since'"
    using Mapping_upd_set_keys by (fastforce simp add: tuple_since'_def)
  have lin_data_prev': "linearize data_prev' = linearize data_prev @ [(nt, X)]"
    unfolding data_prev'_def append_queue_rep ..
  have wf_data_prev': "\<And>as. as \<in> \<Union>(snd ` (set (linearize data_prev'))) \<Longrightarrow> wf_tuple R as"
    unfolding lin_data_prev' using table_X valid_before
    by (auto simp add: table_def n_def R_def)
  have lin_data_in': "linearize data_in' = linearize data_in @ [(nt, X)]"
    unfolding data_in'_def append_queue_rep ..
  have table_auxlist': "\<forall>(t, X) \<in> set auxlist'. table R X"
    using table_X table_Un valid_before
    by (auto simp add: auxlist'_def n_def R_def split: list.splits if_splits)
  have lookup_tuple_since': "\<forall>as \<in> Mapping.keys tuple_since'.
    case Mapping.lookup tuple_since' as of Some t \<Rightarrow> t \<le> nt"
    unfolding tuple_since'_def using valid_before Mapping_lookup_upd_set[of tuple_since]
    by (auto dest: Mapping.in_keysD intro!: Mapping_keys_intro split: if_splits option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    ts_tuple_rel (set auxlist) \<union> ts_tuple_rel {(nt, X)}"
    unfolding auxlist'_def
    using ts_tuple_rel_ext[of _ id] ts_tuple_rel_ext'[of _ id]
      ts_tuple_rel_ext_Cons ts_tuple_rel_ext_Cons'
    by (fastforce simp: ts_tuple_rel_f_def split: list.splits if_splits)
  have valid_tuple_nt_X: "\<And>tas. tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow> valid_tuple tuple_since' tas"
    using valid_before by (auto simp add: X'_def ts_tuple_rel_f_def valid_tuple_def tuple_since'_def
        Mapping_lookup_upd_set dest: Mapping.in_keysD split: option.splits)
  have valid_tuple_mono: "\<And>tas. valid_tuple tuple_since tas \<Longrightarrow> valid_tuple tuple_since' tas"
    by (auto simp add: X'_def valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
        intro: Mapping_keys_intro split: option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in) \<union> {(nt, X)}).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set auxlist')"
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
      using assm[unfolded ts_tuple_rel_auxlist' ts_tuple_rel_Un]
    proof (rule UnE)
      assume assm: "tas \<in> ts_tuple_rel (set auxlist)"
      then have "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)). valid_tuple tuple_since tas}"
        using valid_before by auto
      then show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm by (auto simp only: ts_tuple_rel_Un intro: valid_tuple_mono)
    next
      assume assm: "tas \<in> ts_tuple_rel {(nt, X)}"
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm valid_before by (auto simp add: X'_def ts_tuple_rel_Un tuple_since'_def
            valid_tuple_def Mapping_lookup_upd_set ts_tuple_rel_f_def dest: Mapping.in_keysD
            split: option.splits if_splits)
    qed
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
    then have "tas \<in> (ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in)) - ts_tuple_rel {(nt, X)}) \<union> ts_tuple_rel {(nt, X)}"
      by (auto simp only: ts_tuple_rel_Un)
    then show "tas \<in> ts_tuple_rel (set auxlist')"
    proof (rule UnE)
      assume assm': "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)) - ts_tuple_rel {(nt, X)}"
      then have tas_in: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in))"
        by (auto simp only: ts_tuple_rel_f_def)
      obtain t as where tas_def: "tas = (t, as)"
        by (cases tas) auto
      have "t \<in> fst ` (set (linearize data_prev) \<union> set (linearize data_in))"
        using assm' unfolding tas_def by (force simp add: ts_tuple_rel_f_def)
      then have t_le_nt: "t \<le> nt"
        using valid_before by auto
      have valid_tas: "valid_tuple tuple_since' tas"
        using assm by auto
      have "valid_tuple tuple_since tas"
      proof (cases "as \<in> Mapping.keys tuple_since")
        case True
        then show ?thesis
          using valid_tas tas_def by (auto simp add: X'_def valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set split: option.splits if_splits)
      next
        case False
        then have "t = nt" "as \<in> X"
          using valid_tas t_le_nt unfolding tas_def
          by (auto simp add: X'_def valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
              intro: Mapping_keys_intro split: option.splits if_splits)
        then have "False"
          using assm' unfolding tas_def ts_tuple_rel_f_def by (auto simp only: ts_tuple_rel_f_def id_def)
        then show ?thesis
          by simp
      qed
      then show "tas \<in> ts_tuple_rel (set auxlist')"
        using tas_in valid_before by (auto simp add: ts_tuple_rel_auxlist')
    qed (auto simp only: ts_tuple_rel_auxlist')
  qed
  have table_since: "table (args_R args) (Mapping.keys tuple_since)"
    using valid_before by (auto simp add: table_def)
  have keys_tuple_since': "Mapping.keys tuple_since \<union> X' = Mapping.keys tuple_since'"
    using valid_before
    by (auto simp: tuple_since'_def Mapping_upd_set_keys)
  have sig_since: "wf_table_sig wf_table_since = args_R args"
    and set_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by auto
  have sig_since'': "wf_table_sig (wf_table_upd args tuple_since' (\<lambda>_. wf_table_union wf_table_since (wf_table_of_set_args args X'))) = args_R args"
    and sig_since: "wf_table_sig wf_table_since = args_R args"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto intro!: wf_table_sig_upd simp: wf_table_sig_union wf_table_sig_args)
  have table_X': "table (args_R args) X'"
    using assms(2)
    by (auto simp: X'_def table_def)
  have distR: "distinct (args_R args)"
    using valid_before by auto
  have keys_tuple_since'': "wf_table_set (wf_table_upd args tuple_since' (\<lambda>_. wf_table_union wf_table_since (wf_table_of_set_args args X'))) = Mapping.keys tuple_since'"
    by (rule wf_table_set_upd[OF distR table_since'[unfolded n_def R_def]])
      (auto simp: keys_tuple_since'[symmetric] set_since[symmetric]
        wf_table_set_union sig_since wf_table_sig_args[OF distR] wf_table_of_set_args[OF distR table_X'])
  have table_in: "table (args_R args) (Mapping.keys tuple_in)"
    using valid_before by (auto simp add: table_def)
  have keys_tuple_in: "table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have keys_tuple_in': "table_in \<union> X = Mapping.keys tuple_in'"
    using valid_before
    by (auto simp: tuple_in'_def Mapping_upd_set_keys)
  have sig_in: "wf_table_sig wf_table_in = args_R args"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have sig_in'': "wf_table_sig (wf_table_upd args tuple_in' (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args X))) = args_R args"
    and sig_since: "wf_table_sig wf_table_since = args_R args"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto intro!: wf_table_sig_upd simp: wf_table_sig_union wf_table_sig_args)
  have keys_tuple_in'': "wf_table_set (wf_table_upd args tuple_in' (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args X))) = Mapping.keys tuple_in'"
    by (rule wf_table_set_upd[OF distR table_in'[unfolded n_def R_def]])
      (auto simp: keys_tuple_in keys_tuple_in'[symmetric] set_in[symmetric]
        wf_table_set_union sig_in wf_table_sig_args[OF distR] wf_table_of_set_args[OF distR table_X])
  show ?thesis
  proof (cases "memL I 0")
    case True
    then have add_def: "add_new_table_mmsaux args X (nt, gc, data_prev, data_in,
      table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) = (nt, gc, data_prev, data_in',
      table_in \<union> X, wf_table_upd args tuple_in' (\<lambda>_. wf_table_union wf_table_in (wf_table_of_set_args args X)), tuple_in', wf_table_since', tuple_since')"
      unfolding data_in'_def tuple_in'_def tuple_since'_def wf_table_since'_def X'_def
      by (auto simp: Let_def I_def minus_keys_def)
    have "\<forall>t \<in> fst ` set (linearize data_in'). t \<le> nt \<and> memL I (nt - t)"
      using valid_before True by (auto simp add: lin_data_in')
    moreover have "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof -
      fix as
      show "Mapping.lookup tuple_in' as = safe_max (fst `
        {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since' tas \<and> as = snd tas})"
      proof (cases "as \<in> X")
        case True
        have "valid_tuple tuple_since' (nt, as)"
          using True valid_before by (auto simp add: X'_def valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set dest: Mapping.in_keysD split: option.splits)
        moreover have "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          using True by (auto simp add: ts_tuple_rel_f_def)
        ultimately have nt_in: "nt \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas}"
        proof -
          assume a1: "valid_tuple tuple_since' (nt, as)"
          assume "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          then have "\<exists>p. nt = fst p \<and> p \<in> ts_tuple_rel (insert (nt, X)
            (set (linearize data_in))) \<and> valid_tuple tuple_since' p \<and> as = snd p"
            using a1 by simp
          then show "nt \<in> fst ` {p \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in))).
            valid_tuple tuple_since' p \<and> as = snd p}"
            by blast
        qed
        moreover have "\<And>t. t \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas} \<Longrightarrow> t \<le> nt"
          using valid_before by (auto split: option.splits)
            (metis (no_types, lifting) eq_imp_le fst_conv insertE ts_tuple_rel_dest)
        ultimately have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)
          \<union> set [(nt, X)]). valid_tuple tuple_since' tas \<and> as = snd tas}) = nt"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of _ "linearize data_in'"],
              unfolded lin_data_in' set_append]
          by (metis (mono_tags) Un_empty_right Un_insert_right empty_set list.simps(15))
        then show ?thesis
          using nt_in True
          by (auto simp add: tuple_in'_def Mapping_lookup_upd_set safe_max_def lin_data_in')
      next
        case False
        have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since tas \<and> as = snd tas} =
          {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using False by (fastforce simp add: X'_def lin_data_in' ts_tuple_rel_f_def valid_tuple_def
              tuple_since'_def Mapping_lookup_upd_set intro: Mapping_keys_intro
              split: option.splits if_splits)
        then show ?thesis
          using valid_before False
          by (auto simp add: tuple_in'_def Mapping_lookup_upd_set newest_tuple_in_mapping_def)
      qed
    qed
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_in)"]
        lookup_tuple_since' ts_tuple_rel_auxlist'
        table_in' keys_tuple_in' sig_in'' keys_tuple_in''
        table_since' keys_tuple_since' sig_since'' keys_tuple_since''
      unfolding add_def auxlist'_def[symmetric] wf_table_since'_def[symmetric] cur_nt I_def
      by (auto simp only: valid_mmsaux.simps lin_data_in' n_def R_def) (auto simp: table_def)
  next
    case False
    then have add_def: "add_new_table_mmsaux args X (nt, gc, data_prev, data_in,
      table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) = (nt, gc, data_prev', data_in,
      table_in, wf_table_in, tuple_in, wf_table_since', tuple_since')"
      unfolding I_def data_prev'_def tuple_since'_def wf_table_since'_def X'_def
      by (auto simp: Let_def minus_keys_def)
    have "\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> nt \<and> \<not> memL I (nt - t)"
      using valid_before False by (auto simp add: lin_data_prev' I_def)
    moreover have "\<And>as. {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since tas \<and> as = snd tas} =
      {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since' tas \<and> as = snd tas}"
    proof (rule set_eqI, rule iffI)
      fix as tas
      assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas}"
      then obtain t Z where Z_def: "tas = (t, as)" "as \<in> Z" "(t, Z) \<in> set (linearize data_in)"
        "valid_tuple tuple_since' (t, as)"
        by (auto simp add: ts_tuple_rel_f_def)
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
      using assm
      proof (cases "as \<in> Mapping.keys tuple_since")
        case False
        then have "t \<ge> nt"
          using Z_def(4) by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set intro: Mapping_keys_intro split: option.splits if_splits)
        then show ?thesis
          using Z_def(3) valid_before \<open>\<not> memL I 0\<close> unfolding I_def by auto
      qed (auto simp add: X'_def valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
           dest: Mapping.in_keysD split: option.splits)
    qed (auto simp add: X'_def Mapping_lookup_upd_set valid_tuple_def tuple_since'_def
         intro: Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_prev)"]
        False lookup_tuple_since' ts_tuple_rel_auxlist' wf_data_prev'
        valid_before table_since' keys_tuple_since' sig_since'' keys_tuple_since'' table_in'
      unfolding add_def auxlist'_def[symmetric] wf_table_since'_def[symmetric] cur_nt I_def n_def R_def
        valid_mmsaux.simps
      by (fastforce simp: lin_data_prev')
  qed
qed

lemma valid_add_new_table_mmsaux:
  assumes valid_before: "valid_mmsaux args cur aux auxlist"
  and table_X: "table (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X aux)
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
  using valid_add_new_table_mmsaux_unfolded assms
  by (cases aux) fast

subsection \<open>Result and interpretation\<close>

lemma foldr_ts_tuple_rel:
  "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {} \<longleftrightarrow>
  (\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t)"
  by (auto simp: foldr_union ts_tuple_rel_f_def)

lemma valid_result_mmsaux_unfolded:
  assumes "valid_mmsaux args cur
    (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  shows "result_mmsaux args (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
proof -
  have res: "result_mmsaux args (t, gc, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since tas}"
    using assms valid_mmsaux_tuple_in_keys[OF assms]
    by auto
  have ts_tuple_rel_in: "(a, b) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow> memL (args_ivl args) (cur - a)" for a b
    using assms
    by (auto dest!: ts_tuple_rel_dest)
  have ts_tuple_rel_prev: "(a, b) \<in> ts_tuple_rel (set (linearize data_prev)) \<Longrightarrow> \<not>memL (args_ivl args) (cur - a)" for a b
    using assms
    by (auto dest!: ts_tuple_rel_dest)
  have ts_tuple_rel_auxlist: "ts_tuple_rel (set auxlist) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas}"
    using assms
    by auto
  show ?thesis
    using ts_tuple_rel_in ts_tuple_rel_prev
    by (auto simp del: result_mmsaux.simps simp: res foldr_ts_tuple_rel ts_tuple_rel_auxlist
        ts_tuple_rel_Un image_snd)+
qed

lemma valid_result_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  result_mmsaux args aux = foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
  using valid_result_mmsaux_unfolded by (cases aux) fast

lemma valid_result_mmsaux': "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  result_mmsaux' args aux =
  eval_args_agg args (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
  by (simp add: result_mmsaux'_def valid_result_mmsaux)

interpretation default_msaux: msaux valid_mmsaux init_mmsaux add_new_ts_mmsaux gc_join_mmsaux
  add_new_table_mmsaux result_mmsaux'
  using valid_init_mmsaux valid_add_new_ts_mmsaux valid_gc_join_mmsaux valid_add_new_table_mmsaux
    valid_result_mmsaux'
  by unfold_locales assumption+

(*<*)
end
(*>*)
