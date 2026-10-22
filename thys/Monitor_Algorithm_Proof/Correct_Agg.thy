(*<*)
theory Correct_Agg
  imports
    "Monitor_Algorithm.Monitor" 
    Progress
begin
(*>*)


subsection \<open> Lift envs \<close>

definition lift_envs' :: "nat \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "lift_envs' b R = (\<lambda>(xs,ys). xs @ ys) ` ({xs. length xs = b} \<times> R)"

lemma lift_envs'_0[simp]: "lift_envs' 0 R = R"
  by (auto simp: lift_envs'_def image_iff)

text \<open>The group key of a tuple of the aggregated formula: its columns that are not bound by the
  aggregation, read as columns of the aggregation's result.\<close>

lemma tup_get_agg_key:
  assumes "c \<in> set cs" "k \<le> c"
  shows "tup_get (shift_cols k cs) (agg_key k cs x) (c - k) = tup_get cs x c"
proof -
  have "tup_get (shift_cols k cs) (agg_key k cs x) (c - k) =
    tup_get (filter (\<lambda>x. k \<le> x) cs) (agg_key k cs x) c"
    unfolding shift_cols_def using assms
    by (intro tup_get_map) (auto simp: inj_on_def)
  also have "\<dots> = tup_get cs x c"
    unfolding agg_key_def using assms by (simp add: tup_get_restrict)
  finally show ?thesis .
qed

lemma wf_tuple_agg_key[simp]: "wf_tuple (shift_cols k cs) (agg_key k cs x)"
  by (simp add: agg_key_def shift_cols_def wf_tuple_def)

lemma mem_restr_lift_envs'_iff:
  assumes "distinct cs"
  shows "mem_restr (lift_envs' k R) cs x \<longleftrightarrow>
    wf_tuple cs x \<and> mem_restr R (shift_cols k cs) (agg_key k cs x)"
proof
  assume "mem_restr (lift_envs' k R) cs x"
  then obtain w where w: "w \<in> lift_envs' k R" "wf_tuple cs x"
    "\<forall>c\<in>set cs. c < length w \<and> w ! c = tup_get cs x c"
    by (auto elim: mem_restrE[OF _ assms])
  then obtain xs ys where xs: "w = xs @ ys" "length xs = k" "ys \<in> R"
    by (auto simp: lift_envs'_def)
  have "mem_restr R (shift_cols k cs) (agg_key k cs x)"
  proof (rule mem_restrI[OF distinct_shift_cols[OF assms] xs(3) wf_tuple_agg_key], intro ballI)
    fix d
    assume "d \<in> set (shift_cols k cs)"
    then obtain c where c: "c \<in> set cs" "k \<le> c" "d = c - k"
      by (auto simp: set_shift_cols)
    then show "d < length ys \<and> ys ! d = tup_get (shift_cols k cs) (agg_key k cs x) d"
      using w(3) xs by (auto simp: tup_get_agg_key nth_append)
  qed
  with w(2) show "wf_tuple cs x \<and> mem_restr R (shift_cols k cs) (agg_key k cs x)" ..
next
  assume *: "wf_tuple cs x \<and> mem_restr R (shift_cols k cs) (agg_key k cs x)"
  then obtain ys where ys: "ys \<in> R"
    "\<forall>d\<in>set (shift_cols k cs). d < length ys \<and> ys ! d = tup_get (shift_cols k cs) (agg_key k cs x) d"
    by (auto elim: mem_restrE[OF _ distinct_shift_cols[OF assms]])
  let ?w = "map (tup_get cs x) [0..<k] @ ys"
  have w: "?w \<in> lift_envs' k R"
    using ys(1) by (auto simp: lift_envs'_def image_iff)
  have get: "\<forall>c\<in>set cs. c < length ?w \<and> ?w ! c = tup_get cs x c"
  proof
    fix c
    assume c: "c \<in> set cs"
    show "c < length ?w \<and> ?w ! c = tup_get cs x c"
    proof (cases "c < k")
      case False
      then have "c - k \<in> set (shift_cols k cs)"
        using c by (auto simp: set_shift_cols)
      then show ?thesis
        using ys(2) False c by (auto simp: nth_append tup_get_agg_key)
    qed (simp add: nth_append)
  qed
  show "mem_restr (lift_envs' k R) cs x"
    by (rule mem_restrI[OF assms w *[THEN conjunct1] get])
qed


subsection \<open> Aggregators' qtable \<close>

definition "agg_n args = (case args_agg args of None \<Rightarrow> args_n args | Some aggargs \<Rightarrow> aggargs_n aggargs)"

definition "agg_tys args = (case args_agg args of None \<Rightarrow> []           | Some aggargs \<Rightarrow> aggargs_tys aggargs)"

lemma progress_packagg[simp]: "Progress.progress \<sigma> P (packagg args \<phi>) j = Progress.progress \<sigma> P \<phi> j"
  by (auto simp: packagg_def split: option.splits)

text \<open>A temporal operator's table, after the aggregation if any, is over @{const args_cols}.\<close>

lemma fv_list_packagg:
  assumes valid: "valid_aggargs n (Formula.fv_list \<psi>) (args_agg args)"
    and R: "args_R args = Formula.fv_list \<psi>"
    and fv: "Formula.fv_list \<chi> = Formula.fv_list \<psi>"
  shows "Formula.fv_list (packagg args \<chi>) = args_cols args"
proof (cases "args_agg args")
  case None
  then show ?thesis
    by (simp add: packagg_def args_cols_def R fv)
next
  case (Some aggargs)
  let ?k = "length (aggargs_tys aggargs)"
  let ?y = "aggargs_y aggargs"
  from Some valid have cols: "aggargs_cols aggargs = Formula.fv_list \<psi>" and safe: "safe_aggargs aggargs"
    by (simp_all add: valid_aggargs_def)
  have set_cols: "set (aggargs_cols aggargs) = Formula.fv \<chi>"
    unfolding cols fv[symmetric] by simp
  from safe have fresh: "?y + ?k \<notin> Formula.fv \<chi>"
    and f_fv: "Formula.fv_trm (aggargs_f aggargs) \<subseteq> Formula.fv \<chi>"
    by (simp_all add: safe_aggargs_def set_cols)
  have sub: "set (Formula.fvi_trm_list ?k (aggargs_f aggargs)) \<subseteq> set (Formula.fvi_list ?k \<chi>)"
    using f_fv by (auto simp: fvi_trm_iff_fv_trm[of _ ?k] fvi_iff_fv[of _ ?k])
  have y_notin: "?y \<notin> set (Formula.fvi_list ?k \<chi>)"
    using fresh fvi_iff_fv[of ?y ?k \<chi>] by simp
  have "Formula.fv_list (packagg args \<chi>) = cols_union [?y] (Formula.fvi_list ?k \<chi>)"
    by (simp add: packagg_def Some cols_union_subset[OF sub])
  also have "\<dots> = ?y # Formula.fvi_list ?k \<chi>"
    using y_notin by (auto simp: cols_union_def filter_id_conv)
  also have "\<dots> = args_cols args"
    using fvi_list_plus[of 0 ?k \<chi>] by (simp add: args_cols_def Some R fv)
  finally show ?thesis .
qed

lemma fv_packagg_less:
  assumes valid: "valid_aggargs n (Formula.fv_list \<psi>) (args_agg args)"
    and fv_sub: "Formula.fv \<chi> \<subseteq> Formula.fv \<psi>"
    and args_n: "args_n args = n"
    and bound: "\<forall>x\<in>Formula.fv \<psi>. x < n"
  shows "\<forall>x\<in>Formula.fv (packagg args \<chi>). x < agg_n args"
proof (cases "args_agg args")
  case None
  with args_n have pk: "packagg args \<chi> = \<chi>" and an: "agg_n args = n"
    by (simp_all add: packagg_def agg_n_def)
  show ?thesis
    unfolding pk an using fv_sub bound by blast
next
  case (Some aggargs)
  let ?b = "length (aggargs_tys aggargs)"
  from Some valid have cols: "Formula.fv \<psi> = set (aggargs_cols aggargs)" and safe: "safe_aggargs aggargs"
    by (simp_all add: valid_aggargs_def flip: set_fvi_list)
  from safe have y_less: "aggargs_y aggargs < aggargs_n aggargs"
    and cols_less: "\<forall>i\<in>set (aggargs_cols aggargs). i < ?b + aggargs_n aggargs"
    and f_cols: "Formula.fv_trm (aggargs_f aggargs) \<subseteq> set (aggargs_cols aggargs)"
    by (simp_all add: safe_aggargs_def)
  have x_less: "x < aggargs_n aggargs" if x: "x \<in> Formula.fv (packagg args \<chi>)" for x
  proof -
    from Some x consider (chi) "x + ?b \<in> Formula.fv \<chi>"
      | (f) "x + ?b \<in> Formula.fv_trm (aggargs_f aggargs)" | (y) "x = aggargs_y aggargs"
      by (auto simp: packagg_def fvi_iff_fv[where b="length (aggargs_tys aggargs)"]
          fvi_trm_iff_fv_trm[where b="length (aggargs_tys aggargs)"])
    then show ?thesis
    proof cases
      case chi
      with fv_sub cols have "x + ?b \<in> set (aggargs_cols aggargs)"
        by blast
      with cols_less have "x + ?b < ?b + aggargs_n aggargs"
        by (rule bspec)
      then show ?thesis
        by simp
    next
      case f
      with f_cols have "x + ?b \<in> set (aggargs_cols aggargs)"
        by blast
      with cols_less have "x + ?b < ?b + aggargs_n aggargs"
        by (rule bspec)
      then show ?thesis
        by simp
    next
      case y
      with y_less show ?thesis
        by simp
    qed
  qed
  from Some have "agg_n args = aggargs_n aggargs"
    by (simp add: agg_n_def)
  with x_less show ?thesis
    by simp
qed

lemma qtable_eval_agg:
  assumes inner: "qtable cs (mem_restr (lift_envs' (length tys) R) cs)
      (\<lambda>v. Formula.sat \<sigma> V (val (length tys + n) cs v) i \<phi>) rel"
    and cs: "distinct cs" "set cs = Formula.fv \<phi>"
    and n: "\<forall>x\<in>Formula.fv (Formula.Agg y \<omega> tys f \<phi>). x < n"
    and fresh: "y + length tys \<notin> Formula.fv \<phi>"
    and b_fv: "{0..<length tys} \<subseteq> Formula.fv \<phi>"
    and f_fv: "Formula.fv_trm f \<subseteq> Formula.fv \<phi>"
    and g0: "g0 = (Formula.fv \<phi> \<subseteq> {0..<length tys})"
  shows "qtable (y # shift_cols (length tys) cs) (mem_restr R (y # shift_cols (length tys) cs))
      (\<lambda>v. Formula.sat \<sigma> V (val n (y # shift_cols (length tys) cs) v) i (Formula.Agg y \<omega> tys f \<phi>))
      (eval_agg cs g0 \<omega> tys f rel)"
proof -
  let ?k = "length tys"
  let ?scs = "shift_cols ?k cs"
  let ?oc = "y # ?scs"
  let ?key = "agg_key ?k cs"
  define M where "M = (\<lambda>v. {(x, ecard Zs) | x Zs.
      Zs = {zs. length zs = ?k \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and>
      Zs \<noteq> {}})"
  have sat_Agg: "Formula.sat \<sigma> V v i (Formula.Agg y \<omega> tys f \<phi>) \<longleftrightarrow>
    (M v = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<?k}) \<and> v ! y = eval_agg_op \<omega> (M v)" for v
    unfolding M_def by simp
  have fv_n: "c < ?k + n" if "c \<in> fv \<phi>" for c
  proof (cases "?k \<le> c")
    case True
    with that have "c - ?k \<in> Formula.fvi ?k \<phi>"
      by (simp add: fvi_iff_fv[where b= ?k])
    with n have "c - ?k < n"
      by simp
    with True show ?thesis
      by simp
  qed simp
  have y_n: "y < n"
    using n by simp
  have y_notin: "y \<notin> set ?scs"
    using fresh cs(2) by (auto simp: set_shift_cols)
  have scs: "distinct ?scs"
    by (rule distinct_shift_cols[OF cs(1)])
  have wf_rel: "wf_tuple cs x" if "x \<in> rel" for x
    using that qtable_wf_tupleD[OF inner] by blast
  have env_y: "val n ?oc (a # kk) ! y = a" for a :: event_data and kk
    using y_n by (simp add: tup_get_Cons)
  have env_c: "val n ?oc (a # kk) ! (c - ?k) = tup_get ?scs kk (c - ?k)"
    if "c \<in> set cs" "?k \<le> c" for a :: event_data and kk c  proof -
    have "c < ?k + n" "c \<noteq> y + ?k"
      using that(1) fresh fv_n cs(2) by auto
    then have "c - ?k \<noteq> y" "c - ?k < n"
      using that(2) by auto
    then show ?thesis
      by (simp add: tup_get_Cons)
  qed
  define bt :: "event_data list \<Rightarrow> event_data tuple \<Rightarrow> event_data tuple"
    where "bt = (\<lambda>zs kk. map (\<lambda>c. if c < ?k then zs ! c else tup_get ?scs kk (c - ?k)) cs)"  have wf_bt: "wf_tuple cs (bt zs kk)" for zs kk
    by (simp add: bt_def wf_tuple_def)
  have tup_bt: "tup_get cs (bt zs kk) c = (if c < ?k then zs ! c else tup_get ?scs kk (c - ?k))"
    if "c \<in> set cs" for zs kk c
    using that by (simp add: bt_def tup_get_map_self)
  have key_bt: "?key (bt zs kk) = kk" if "wf_tuple ?scs kk" for zs kk
  proof -
    have "?key (bt zs kk) = map (\<lambda>c. tup_get ?scs kk (c - ?k)) (filter (\<lambda>x. ?k \<le> x) cs)"
      unfolding agg_key_def restrict_def by (rule map_cong) (auto simp: tup_bt)
    also have "\<dots> = map (tup_get ?scs kk) ?scs"
      by (simp add: shift_cols_def)
    also have "\<dots> = kk"
      using restrict_idle[OF scs that] by (simp add: restrict_def)
    finally show ?thesis .
  qed
  have bt_key: "bt (map (tup_get cs x) [0..<?k]) (?key x) = x" if "wf_tuple cs x" for x
  proof -
    have "bt (map (tup_get cs x) [0..<?k]) (?key x) = map (tup_get cs x) cs"
      unfolding bt_def by (rule map_cong) (auto simp: tup_get_agg_key)
    also have "\<dots> = x"
      using restrict_idle[OF cs(1) that] by (simp add: restrict_def)
    finally show ?thesis .
  qed
  have agree_bt: "val (?k + n) cs (bt zs kk) ! c = (zs @ val n ?oc (a # kk)) ! c"
    if "length zs = ?k" "c \<in> fv \<phi>" for zs kk a c
    using that cs(2) fv_n[OF that(2)] env_c[of c a kk] by (auto simp: tup_bt nth_append)
  have sat_bt: "Formula.sat \<sigma> V (val (?k + n) cs (bt zs kk)) i \<phi> \<longleftrightarrow>
    Formula.sat \<sigma> V (zs @ val n ?oc (a # kk)) i \<phi>" if "length zs = ?k" for zs kk a
    using agree_bt[OF that] by (intro sat_fv_cong) blast
  have eval_bt: "meval_trm cs f (bt zs kk) = Formula.eval_trm (zs @ val n ?oc (a # kk)) f"
    if "length zs = ?k" for zs kk a
  proof -
    have "meval_trm cs f (bt zs kk) = Formula.eval_trm (val (?k + n) cs (bt zs kk)) f"
      using f_fv cs(2) fv_n by (intro meval_trm_eval_trm) auto
    also have "\<dots> = Formula.eval_trm (zs @ val n ?oc (a # kk)) f"
      using agree_bt[OF that] f_fv by (intro eval_trm_fv_cong) blast
    finally show ?thesis .
  qed
  have inj_bt: "inj_on (\<lambda>zs. bt zs kk) {zs. length zs = ?k}" for kk
  proof (rule inj_onI)
    fix zs zs'
    assume zs: "zs \<in> {zs. length zs = ?k}" "zs' \<in> {zs. length zs = ?k}" "bt zs kk = bt zs' kk"
    show "zs = zs'"
    proof (rule nth_equalityI)
      show "length zs = length zs'"
        using zs by simp
      fix c
      assume "c < length zs"
      then have "c < ?k" "c \<in> set cs"
        using zs(1) b_fv cs(2) by auto
      then show "zs ! c = zs' ! c"
        using tup_bt[of c zs kk] tup_bt[of c zs' kk] zs(3) by simp
    qed  qed
  define M' where "M' = (\<lambda>kk. let group = Set.filter (\<lambda>x. ?key x = kk) rel
    in (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group)"
  have M'_M: "M' kk = M (val n ?oc (a # kk))" if kk: "wf_tuple ?scs kk" "mem_restr R ?scs kk" for kk a
  proof -
    let ?env = "val n ?oc (a # kk)"
    let ?group = "Set.filter (\<lambda>x. ?key x = kk) rel"
    let ?Zs = "\<lambda>b. {zs. length zs = ?k \<and> Formula.sat \<sigma> V (zs @ ?env) i \<phi> \<and> Formula.eval_trm (zs @ ?env) f = b}"
    have mr_bt: "mem_restr (lift_envs' ?k R) cs (bt zs kk)" for zs
      using kk by (simp add: mem_restr_lift_envs'_iff[OF cs(1)] wf_bt key_bt)
    have grp: "Set.filter (\<lambda>x. meval_trm cs f x = b) ?group = (\<lambda>zs. bt zs kk) ` ?Zs b" for b
    proof (intro set_eqI iffI)
      fix x
      assume x: "x \<in> Set.filter (\<lambda>x. meval_trm cs f x = b) ?group"
      then have x': "x \<in> rel" "?key x = kk" "meval_trm cs f x = b"
        by auto
      let ?zs = "map (tup_get cs x) [0..<?k]"
      have x_eq: "x = bt ?zs kk"
        using bt_key[OF wf_rel[OF \<open>x \<in> rel\<close>]] \<open>?key x = kk\<close> by simp
      have "mem_restr (lift_envs' ?k R) cs x"
        using mr_bt x_eq by metis
      then have "Formula.sat \<sigma> V (val (?k + n) cs x) i \<phi>"
        using inner x'(1) by (auto simp: qtable_iff)
      then have "?zs \<in> ?Zs b"
        using sat_bt[of ?zs kk a] eval_bt[of ?zs kk a] x'(3) by (simp flip: x_eq)
      with x_eq show "x \<in> (\<lambda>zs. bt zs kk) ` ?Zs b"
        by (rule image_eqI)    next
      fix x
      assume "x \<in> (\<lambda>zs. bt zs kk) ` ?Zs b"
      then obtain zs where zs: "x = bt zs kk" "length zs = ?k" "Formula.sat \<sigma> V (zs @ ?env) i \<phi>"
        "Formula.eval_trm (zs @ ?env) f = b"
        by auto
      then have "x \<in> rel"
        using sat_bt[of zs kk a] mr_bt[of zs] wf_bt[of zs kk] by (auto intro!: in_qtableI[OF inner])
      with zs show "x \<in> Set.filter (\<lambda>x. meval_trm cs f x = b) ?group"
        using key_bt[OF kk(1)] eval_bt[of zs kk a] by auto
    qed
    have ecard: "ecard (Set.filter (\<lambda>x. meval_trm cs f x = b) ?group) = ecard (?Zs b)" for b
      unfolding grp by (rule ecard_image) (rule inj_on_subset[OF inj_bt], auto)
    have img: "meval_trm cs f ` ?group = {b. ?Zs b \<noteq> {}}"
    proof -
      have "b \<in> meval_trm cs f ` ?group \<longleftrightarrow> Set.filter (\<lambda>x. meval_trm cs f x = b) ?group \<noteq> {}" for b
        by auto
      then show ?thesis
        unfolding grp by auto
    qed
    have "M ?env = (\<lambda>b. (b, ecard (?Zs b))) ` {b. ?Zs b \<noteq> {}}"
      unfolding M_def by auto
    also have "\<dots> = M' kk"
      unfolding M'_def Let_def img[symmetric] ecard by simp
    finally show ?thesis ..
  qed
  have mr_Cons: "wf_tuple ?scs kk \<and> mem_restr R ?scs kk" if "mem_restr R ?oc (a # kk)" for a kk
  proof -
    have wf: "wf_tuple ?scs kk"
      using mem_restr_wf_tuple[OF that] by simp
    have "mem_restr R ?scs (restrict ?scs ?oc (a # kk))"
      using that scs y_notin by (intro restrict_mem_restr) auto
    with wf show ?thesis
      using restrict_Cons_notin[OF y_notin wf scs] by simp
  qed
  show ?thesis
  proof (cases "g0 \<and> rel = empty_table")
    case True
    then have scs_Nil: "?scs = []"
      using cs(2) by (auto simp: g0 shift_cols_def filter_empty_conv)
    show ?thesis
      unfolding qtable_iff
    proof (intro conjI allI impI)
      show "table ?oc (eval_agg cs g0 \<omega> tys f rel)"
        using True scs_Nil by (simp add: eval_agg_def table_def singleton_table_def wf_tuple_def)
      show "finite (eval_agg cs g0 \<omega> tys f rel)"
        using True by (simp add: eval_agg_def singleton_table_def)
      fix v
      assume mr: "mem_restr R ?oc v"
      then obtain a where v: "v = [a]"
        using mem_restr_wf_tuple[OF mr] scs_Nil by (auto simp: wf_tuple_def length_Suc_conv)
      have "M (val n ?oc v) = {}"
      proof -
        have "\<not> Formula.sat \<sigma> V (zs @ val n ?oc (a # [])) i \<phi>" if "length zs = ?k" for zs
        proof
          assume "Formula.sat \<sigma> V (zs @ val n ?oc (a # [])) i \<phi>"
          moreover have "mem_restr (lift_envs' ?k R) cs (bt zs [])"
            using mr_Cons[of a "[]"] mr unfolding v
            by (simp add: mem_restr_lift_envs'_iff[OF cs(1)] wf_bt key_bt scs_Nil)
          ultimately have "bt zs [] \<in> rel"
            using sat_bt[OF that, of "[]" a] wf_bt by (auto intro!: in_qtableI[OF inner])
          with True show False
            by (simp add: empty_table_def)
        qed
        then show ?thesis
          unfolding M_def v by auto
      qed
      then show "v \<in> eval_agg cs g0 \<omega> tys f rel \<longleftrightarrow>
        Formula.sat \<sigma> V (val n ?oc v) i (Formula.Agg y \<omega> tys f \<phi>) \<and> wf_tuple ?oc v"
        unfolding sat_Agg
        using True env_y[of a "[]"] by (simp add: eval_agg_def singleton_table_def g0 v scs_Nil)
    qed
  next
    case non_default: False
    have res: "eval_agg cs g0 \<omega> tys f rel = (\<lambda>kk. eval_agg_op \<omega> (M' kk) # kk) ` ?key ` rel"
      by (simp only: eval_agg_def M'_def Let_def if_not_P[OF non_default])
    show ?thesis
      unfolding qtable_iff res
    proof (intro conjI allI impI)
      show "table ?oc ((\<lambda>kk. eval_agg_op \<omega> (M' kk) # kk) ` ?key ` rel)"
        by (auto simp: table_def)
      show "finite ((\<lambda>kk. eval_agg_op \<omega> (M' kk) # kk) ` ?key ` rel)"
        using qtableD(5)[OF inner] by simp
      fix v
      assume mr: "mem_restr R ?oc v"
      then obtain a kk where v: "v = a # kk"
        using mem_restr_wf_tuple[OF mr] by auto
      from mr_Cons[OF mr[unfolded v]] have kk: "wf_tuple ?scs kk" "mem_restr R ?scs kk"
        by auto
      note M'_eq = M'_M[OF kk, of a]
      show "v \<in> (\<lambda>kk. eval_agg_op \<omega> (M' kk) # kk) ` ?key ` rel \<longleftrightarrow>
        Formula.sat \<sigma> V (val n ?oc v) i (Formula.Agg y \<omega> tys f \<phi>) \<and> wf_tuple ?oc v"
        unfolding sat_Agg
      proof
        assume "v \<in> (\<lambda>kk. eval_agg_op \<omega> (M' kk) # kk) ` ?key ` rel"
        then obtain x where x: "x \<in> rel" "?key x = kk" "a = eval_agg_op \<omega> (M' kk)"
          by (auto simp: v)
        then have "M' kk \<noteq> {}"
          by (auto simp: M'_def Let_def)
        then have "M (val n ?oc v) \<noteq> {}"
          using M'_eq by (simp add: v)
        moreover have "val n ?oc v ! y = eval_agg_op \<omega> (M (val n ?oc v))"
          using x(3) M'_eq env_y[of a kk] unfolding v by metis
        ultimately show "((M (val n ?oc v) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<?k}) \<and>
          val n ?oc v ! y = eval_agg_op \<omega> (M (val n ?oc v))) \<and> wf_tuple ?oc v"
          using kk(1) by (simp add: v)      next
        assume "((M (val n ?oc v) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<?k}) \<and>
          val n ?oc v ! y = eval_agg_op \<omega> (M (val n ?oc v))) \<and> wf_tuple ?oc v"
        then have a: "a = eval_agg_op \<omega> (M' kk)" and M_ne: "M' kk = {} \<Longrightarrow> fv \<phi> \<subseteq> {0..<?k}"
          using M'_eq env_y[of a kk] by (simp_all add: v)
        obtain x where x: "x \<in> rel" "?key x = kk"        proof (cases "M' kk = {}")
          case True
          then have "g0" "?scs = []"
            using M_ne cs(2) by (auto simp: g0 shift_cols_def filter_empty_conv)
          with non_default obtain x where "x \<in> rel"
            by (auto simp: empty_table_def)
          moreover have "?key x = kk"
            using kk(1) wf_tuple_agg_key[of ?k cs x] \<open>?scs = []\<close> by simp
          ultimately show thesis
            by (rule that)
        next
          case False
          then show thesis
            using that by (auto simp: M'_def Let_def)
        qed
        then show "v \<in> (\<lambda>kk. eval_agg_op \<omega> (M' kk) # kk) ` ?key ` rel"
          using a by (auto simp: v image_iff intro!: bexI[OF _ x(1)])
      qed
    qed
  qed
qed

lemma qtable_eval_args_agg:
  "qtable (args_cols args) (mem_restr R' (args_cols args))
    (\<lambda>v. Formula.sat \<sigma> V (val (agg_n args) (args_cols args) v) ne (packagg args \<psi>)) (eval_args_agg args rel)"
  if q: "qtable (args_R args) (mem_restr R (args_R args))
      (\<lambda>v. Formula.sat \<sigma> V (val (args_n args) (args_R args) v) ne \<psi>) rel"
    and mr: "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
    and valid_aggargs: "valid_aggargs (args_n args) (args_R args) (args_agg args)"
    and fv: "set (args_R args) = fv \<psi>"
proof (cases "args_agg args")
  case None
  have pack: "packagg args \<psi> = \<psi>"
    by (auto simp add: packagg_def None)
  have "mem_restr R' = mem_restr R"
    using mr by (auto simp: agg_tys_def None)
  then show ?thesis
    using q
    unfolding pack
    by (auto simp: eval_args_agg_def agg_n_def args_cols_def None)
next
  case (Some aggargs)
  have n_def: "agg_n args = aggargs_n aggargs" "args_n args = length (aggargs_tys aggargs) + aggargs_n aggargs"
    using valid_aggargs
    by (auto simp: agg_n_def Some valid_aggargs_def)
  let ?b = "length (aggargs_tys aggargs)"
  have cols: "args_R args = aggargs_cols aggargs" and safe: "safe_aggargs aggargs"
    using valid_aggargs by (simp_all add: valid_aggargs_def Some)
  have x_in_colsD: "x + ?b \<in> fv \<psi> \<Longrightarrow> x < aggargs_n aggargs" for x
    using safe fv by (auto simp: safe_aggargs_def cols)
  show ?thesis
    unfolding packagg_def eval_args_agg_def Some option.case eval_aggargs_def n_def(1) args_cols_def cols
  proof (rule qtable_eval_agg)
    show "qtable (aggargs_cols aggargs) (mem_restr (lift_envs' ?b R') (aggargs_cols aggargs))
      (\<lambda>v. Formula.sat \<sigma> V (val (?b + aggargs_n aggargs) (aggargs_cols aggargs) v) ne \<psi>) rel"
      using q mr by (simp add: n_def agg_tys_def Some cols)
    show "\<forall>x\<in>fv (Formula.Agg (aggargs_y aggargs) (aggargs_\<omega> aggargs) (aggargs_tys aggargs)
      (aggargs_f aggargs) \<psi>). x < aggargs_n aggargs"
    proof
      fix x
      assume "x \<in> fv (Formula.Agg (aggargs_y aggargs) (aggargs_\<omega> aggargs) (aggargs_tys aggargs)
        (aggargs_f aggargs) \<psi>)"
      then consider "x + ?b \<in> fv \<psi>" | "x + ?b \<in> fv_trm (aggargs_f aggargs)" | "x = aggargs_y aggargs"
        by (auto simp: fvi_iff_fv[where b= ?b] fvi_trm_iff_fv_trm[where b= ?b] split: if_splits)
      then show "x < aggargs_n aggargs"
        using safe fv by cases (auto simp: safe_aggargs_def cols intro: x_in_colsD)
    qed
  qed (use safe fv in \<open>simp_all add: safe_aggargs_def cols\<close>)
qed

(*<*)
end
(*>*)