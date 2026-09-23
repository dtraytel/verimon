(*<*)
theory Dense_Agg_Upkeep
  imports Dense_Agg_Code
begin
(*>*)

section \<open>The aggregation over a window, kept up in one pass per table\<close>

text \<open>
  When a time point's table enters the window of a fused aggregation (@{const usa_add_new_table})
  or leaves it (@{const usa_expire}), the node updates two structures: the count of every tuple in
  the window (@{const ucnt_add}, @{const ucnt_del}), and the kernel's per-group aggregate, which
  sees only the tuples that newly enter or finally leave (@{const uag_ins}, @{const uag_del}).
  As defined, the second builds two tables on the way -- the tuples whose count says they enter
  (@{const ucnt_enter}), then the same tuples widened to the kernel's frame
  (@{const udagg_wide}) -- only for the kernel to fold over them once, and it reads every
  tuple's count again although the first pass just did.

  The kernel's folds commute, so they can run over the table's own sorted list; the widening is
  injective on tuples of the right length, so it can be applied tuple by tuple; and the tuples of
  a table are distinct, so each one's count can be read and updated in the same pass without
  seeing another tuple's update.  @{text cnt_ins_fold} and @{text cnt_del_fold} are that pass,
  and @{text uag_step_ins_eq} and @{text uag_step_del_eq} below say that they compute
  exactly the two structures the two passes did, under a guard -- the table is finite and its
  tuples have the widening's length -- that the code tests and that falls back to the two passes.
\<close>

subsection \<open>A fold over a widened, filtered table is a fold over its list\<close>

lemma fold_image_filter_list:
  assumes F: "comp_fun_commute_on UNIV F" and d: "distinct xs" and inj: "inj_on g (set xs)"
  shows "Finite_Set.fold F b (g ` Set.filter P (set xs))
       = fold (\<lambda>t acc. if P t then F (g t) acc else acc) xs b"
proof -
  have img: "g ` Set.filter P (set xs) = set (map g (filter P xs))" by auto
  have dm: "distinct (map g (filter P xs))"
    using d inj by (simp add: distinct_map inj_on_subset[of g "set xs"])
  have "Finite_Set.fold F b (g ` Set.filter P (set xs))
      = Finite_Set.fold F b (set (map g (filter P xs)))"
    by (simp only: img)
  also have "\<dots> = fold F (remdups (map g (filter P xs))) b"
    by (rule comp_fun_commute_on.fold_set_fold_remdups[OF F]) simp
  also have "\<dots> = fold F (map g (filter P xs)) b"
    by (simp only: distinct_remdups_id[OF dm])
  also have "\<dots> = fold (\<lambda>t acc. if P t then F (g t) acc else acc) xs b"
    by (induct xs arbitrary: b) simp_all
  finally show ?thesis .
qed

lemma udwiden_inj:
  "length xs = count_list bs True \<Longrightarrow> length ys = count_list bs True \<Longrightarrow>
   udwiden bs xs = udwiden bs ys \<Longrightarrow> xs = ys"
proof (induct bs arbitrary: xs ys)
  case (Cons b bs)
  show ?case
  proof (cases b)
    case True
    with Cons show ?thesis by (cases xs; cases ys) auto
  qed (use Cons in auto)
qed simp

lemma inj_on_udwiden: "inj_on (udwiden bs) {xs. length xs = count_list bs True}"
  by (rule inj_onI) (auto intro: udwiden_inj)

subsection \<open>The counts and the aggregate, in one pass\<close>

definition cnt_ins_fold :: "(event_data tuple \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (event_data list \<Rightarrow> event_data tuple) \<Rightarrow>
    event_data list list \<Rightarrow> ucnt \<Rightarrow> 'b \<Rightarrow> ucnt \<times> 'b" where
  "cnt_ins_fold F g xs c b = fold (\<lambda>t (c, acc). case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, F (g t) acc)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, acc)) xs (c, b)"

definition cnt_del_fold :: "(event_data tuple \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (event_data list \<Rightarrow> event_data tuple) \<Rightarrow>
    event_data list list \<Rightarrow> ucnt \<Rightarrow> 'b \<Rightarrow> ucnt \<times> 'b" where
  "cnt_del_fold F g xs c b = fold (\<lambda>t (c, acc). case Mapping.lookup c t of
       None \<Rightarrow> (c, acc)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, if k = 1 then F (g t) acc else acc)
                 else (Mapping.update t (k - 1) c, acc))) xs (c, b)"

lemma lookup_ucnt_add1_other: "u \<noteq> t \<Longrightarrow> Mapping.lookup (ucnt_add1 t c) u = Mapping.lookup c u"
  by (simp add: ucnt_add1_def lookup_update' split: option.splits)

lemma lookup_ucnt_del1_other: "u \<noteq> t \<Longrightarrow> Mapping.lookup (ucnt_del1 t c) u = Mapping.lookup c u"
  by (simp add: ucnt_del1_def lookup_update' lookup_delete split: option.splits)

lemma cnt_ins_fold_eq:
  "distinct xs \<Longrightarrow> cnt_ins_fold F g xs c b =
     (fold ucnt_add1 xs c, fold (\<lambda>t acc. if Mapping.lookup c t = None then F (g t) acc else acc) xs b)"
proof (induct xs arbitrary: c b)
  case (Cons t xs)
  have same: "\<And>b'. fold (\<lambda>u acc. if Mapping.lookup (ucnt_add1 t c) u = None then F (g u) acc else acc) xs b'
      = fold (\<lambda>u acc. if Mapping.lookup c u = None then F (g u) acc else acc) xs b'"
    using Cons.prems by (intro fold_cong refl) (metis distinct.simps(2) lookup_ucnt_add1_other)
  show ?case
    using Cons same
    by (auto simp: cnt_ins_fold_def ucnt_add1_def split: option.splits)
qed (simp add: cnt_ins_fold_def)

lemma cnt_del_fold_eq:
  "distinct xs \<Longrightarrow> cnt_del_fold F g xs c b =
     (fold ucnt_del1 xs c, fold (\<lambda>t acc. if Mapping.lookup c t = Some 1 then F (g t) acc else acc) xs b)"
proof (induct xs arbitrary: c b)
  case (Cons t xs)
  have same: "\<And>b'. fold (\<lambda>u acc. if Mapping.lookup (ucnt_del1 t c) u = Some 1 then F (g u) acc else acc) xs b'
      = fold (\<lambda>u acc. if Mapping.lookup c u = Some 1 then F (g u) acc else acc) xs b'"
    using Cons.prems by (intro fold_cong refl) (metis distinct.simps(2) lookup_ucnt_del1_other)
  show ?case
    using Cons same
    by (auto simp: cnt_del_fold_def ucnt_del1_def split: option.splits)
qed (simp add: cnt_del_fold_def)

subsection \<open>The kernel's steps commute\<close>

lemma cfc_insert_cnt: "comp_fun_commute_on UNIV (insert_cnt args)"
  using insert_cnt_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_insert_sum: "comp_fun_commute_on UNIV (insert_sum args)"
  using insert_sum_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_insert_rank: "comp_fun_commute_on UNIV (insert_rank args ty)"
  using insert_rank_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_delete_cnt: "comp_fun_commute_on UNIV (delete_cnt args)"
  using delete_cnt_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_delete_sum: "comp_fun_commute_on UNIV (delete_sum args)"
  using delete_sum_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_delete_rank: "comp_fun_commute_on UNIV (delete_rank args ty)"
  using delete_rank_comm by unfold_locales (auto simp: fun_eq_iff)

lemma csl_edl:
  "finite (X :: event_data list set) \<Longrightarrow> set (csl X) = X \<and> distinct (csl X)"
  using Dense_Unbox.ID_ccompare_ed by (simp add: csl_finite) (subst csorted_list_of_set_split, auto)

subsection \<open>The two steps of the window, in one pass each\<close>

text \<open>The guard under which the one-pass form applies: the table is finite, which every table
  the monitor builds is, and its tuples have the length the widening expects, which is what
  makes the widening injective.  Where it does not hold, the code falls back to the two passes.\<close>

definition agg_guard :: "daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> bool" where
  "agg_guard p w X \<longleftrightarrow> finite X \<and>
     list_all (\<lambda>t. length t = count_list (wide_mask (Suc w) (dagg_ccols p w)) True) (csl X)"

lemma agg_fold_enter:
  assumes F: "comp_fun_commute_on UNIV F" and g: "agg_guard p w X"
  shows "(ucnt_add X c, Finite_Set.fold F b (udagg_wide p w (ucnt_enter X c)))
       = cnt_ins_fold F (udwiden (wide_mask (Suc w) (dagg_ccols p w))) (csl X) c b"
proof -
  let ?m = "wide_mask (Suc w) (dagg_ccols p w)"
  from g have fin: "finite X" and len: "\<forall>t \<in> set (csl X). length t = count_list ?m True"
    by (auto simp: agg_guard_def list_all_iff)
  from csl_edl[OF fin] have s: "set (csl X) = X" and d: "distinct (csl X)" by auto
  have inj: "inj_on (udwiden ?m) (set (csl X))"
    using len by (intro inj_on_subset[OF inj_on_udwiden]) auto
  have eq: "udagg_wide p w (ucnt_enter X c)
      = udwiden ?m ` Set.filter (\<lambda>t. Mapping.lookup c t = None) (set (csl X))"
    by (simp add: udagg_wide_def udtabw_def ucnt_enter_def s)
  show ?thesis
    unfolding eq fold_image_filter_list[OF F d inj] cnt_ins_fold_eq[OF d] ucnt_add_def ..
qed

lemma agg_fold_leave:
  assumes F: "comp_fun_commute_on UNIV F" and g: "agg_guard p w X"
  shows "(ucnt_del X c, Finite_Set.fold F b (udagg_wide p w (ucnt_leave X c)))
       = cnt_del_fold F (udwiden (wide_mask (Suc w) (dagg_ccols p w))) (csl X) c b"
proof -
  let ?m = "wide_mask (Suc w) (dagg_ccols p w)"
  from g have fin: "finite X" and len: "\<forall>t \<in> set (csl X). length t = count_list ?m True"
    by (auto simp: agg_guard_def list_all_iff)
  from csl_edl[OF fin] have s: "set (csl X) = X" and d: "distinct (csl X)" by auto
  have inj: "inj_on (udwiden ?m) (set (csl X))"
    using len by (intro inj_on_subset[OF inj_on_udwiden]) auto
  have eq: "udagg_wide p w (ucnt_leave X c)
      = udwiden ?m ` Set.filter (\<lambda>t. Mapping.lookup c t = Some 1) (set (csl X))"
    by (simp add: udagg_wide_def udtabw_def ucnt_leave_def s)
  show ?thesis
    unfolding eq fold_image_filter_list[OF F d inj] cnt_del_fold_eq[OF d] ucnt_del_def ..
qed

definition uag_step_ins :: "daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow> aggaux option \<Rightarrow>
    ucnt \<times> aggaux option" where
  "uag_step_ins p w X c ax = (ucnt_add X c, uag_ins p w X c ax)"

definition uag_step_del :: "daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow> aggaux option \<Rightarrow>
    ucnt \<times> aggaux option" where
  "uag_step_del p w X c ax = (ucnt_del X c, uag_del p w X c ax)"

lemma uag_step_ins_eq:
  "uag_step_ins p w X c ax = (if agg_guard p w X then
     (let args = dagg_args p w; g = udwiden (wide_mask (Suc w) (dagg_ccols p w)); xs = csl X in
      case ax of
        None \<Rightarrow> (fold ucnt_add1 xs c, None)
      | Some (CntAux m) \<Rightarrow> (case cnt_ins_fold (insert_cnt args) g xs c (True, m) of
          (c', v, m') \<Rightarrow> (c', if v then Some (CntAux m') else None))
      | Some (SumAux m) \<Rightarrow> (case cnt_ins_fold (insert_sum args) g xs c (True, m) of
          (c', v, m') \<Rightarrow> (c', if v then Some (SumAux m') else None))
      | Some (RankAux (m, ty)) \<Rightarrow> (case cnt_ins_fold (insert_rank args ty) g xs c (True, m) of
          (c', v, m') \<Rightarrow> (c', if v then Some (RankAux (m', ty)) else None)))
   else (ucnt_add X c, uag_ins p w X c ax))"
proof (cases "agg_guard p w X")
  case True
  have fin: "finite (udagg_wide p w (ucnt_enter X c))"
    using True by (simp add: agg_guard_def udagg_wide_def udtabw_def ucnt_enter_def)
  note E = agg_fold_enter[OF _ True, symmetric]
  show ?thesis
  proof (cases ax)
    case None
    then show ?thesis using True by (simp add: uag_step_ins_def uag_ins_def ucnt_add_def)
  next
    case (Some aux)
    then show ?thesis using True fin
      by (cases aux) (auto simp: uag_step_ins_def uag_ins_def Let_def
          E[OF cfc_insert_cnt] E[OF cfc_insert_sum] E[OF cfc_insert_rank] split: prod.splits)
  qed
qed (simp add: uag_step_ins_def)

lemma uag_step_del_eq:
  "uag_step_del p w X c ax = (if agg_guard p w X then
     (let args = dagg_args p w; g = udwiden (wide_mask (Suc w) (dagg_ccols p w)); xs = csl X in
      case ax of
        None \<Rightarrow> (fold ucnt_del1 xs c, None)
      | Some (CntAux m) \<Rightarrow> (case cnt_del_fold (delete_cnt args) g xs c (True, m) of
          (c', v, m') \<Rightarrow> (c', if v then Some (CntAux m') else None))
      | Some (SumAux m) \<Rightarrow> (case cnt_del_fold (delete_sum args) g xs c (True, m) of
          (c', v, m') \<Rightarrow> (c', if v then Some (SumAux m') else None))
      | Some (RankAux (m, ty)) \<Rightarrow> (case cnt_del_fold (delete_rank args ty) g xs c (True, m) of
          (c', v, m') \<Rightarrow> (c', if v then Some (RankAux (m', ty)) else None)))
   else (ucnt_del X c, uag_del p w X c ax))"
proof (cases "agg_guard p w X")
  case True
  note E = agg_fold_leave[OF _ True, symmetric]
  show ?thesis
  proof (cases ax)
    case None
    then show ?thesis using True by (simp add: uag_step_del_def uag_del_def ucnt_del_def)
  next
    case (Some aux)
    then show ?thesis using True
      by (cases aux) (auto simp: uag_step_del_def uag_del_def Let_def
          E[OF cfc_delete_cnt] E[OF cfc_delete_sum] E[OF cfc_delete_rank] split: prod.splits)
  qed
qed (simp add: uag_step_del_def)

text \<open>The same, with the table's list and the mask's length computed once, before the guard, so
  that the generated code neither builds the list twice nor counts the mask for every tuple.\<close>

lemma uag_step_ins_code[code]:
  "uag_step_ins p w X c ax =
    (let msk = wide_mask (Suc w) (dagg_ccols p w); k = count_list msk True; xs = csl X in
     if finite X \<and> list_all (\<lambda>t. length t = k) xs then
       (let args = dagg_args p w; g = udwiden msk in
        case ax of
          None \<Rightarrow> (fold ucnt_add1 xs c, None)
        | Some (CntAux m) \<Rightarrow> (case cnt_ins_fold (insert_cnt args) g xs c (True, m) of
            (c', v, m') \<Rightarrow> (c', if v then Some (CntAux m') else None))
        | Some (SumAux m) \<Rightarrow> (case cnt_ins_fold (insert_sum args) g xs c (True, m) of
            (c', v, m') \<Rightarrow> (c', if v then Some (SumAux m') else None))
        | Some (RankAux (m, ty)) \<Rightarrow> (case cnt_ins_fold (insert_rank args ty) g xs c (True, m) of
            (c', v, m') \<Rightarrow> (c', if v then Some (RankAux (m', ty)) else None)))
     else (ucnt_add X c, uag_ins p w X c ax))"
  unfolding uag_step_ins_eq agg_guard_def Let_def ..

lemma uag_step_del_code[code]:
  "uag_step_del p w X c ax =
    (let msk = wide_mask (Suc w) (dagg_ccols p w); k = count_list msk True; xs = csl X in
     if finite X \<and> list_all (\<lambda>t. length t = k) xs then
       (let args = dagg_args p w; g = udwiden msk in
        case ax of
          None \<Rightarrow> (fold ucnt_del1 xs c, None)
        | Some (CntAux m) \<Rightarrow> (case cnt_del_fold (delete_cnt args) g xs c (True, m) of
            (c', v, m') \<Rightarrow> (c', if v then Some (CntAux m') else None))
        | Some (SumAux m) \<Rightarrow> (case cnt_del_fold (delete_sum args) g xs c (True, m) of
            (c', v, m') \<Rightarrow> (c', if v then Some (SumAux m') else None))
        | Some (RankAux (m, ty)) \<Rightarrow> (case cnt_del_fold (delete_rank args ty) g xs c (True, m) of
            (c', v, m') \<Rightarrow> (c', if v then Some (RankAux (m', ty)) else None)))
     else (ucnt_del X c, uag_del p w X c ax))"
  unfolding uag_step_del_eq agg_guard_def Let_def ..

subsection \<open>The window's two steps, through them\<close>

lemma usa_add_new_table_code[code]:
  "usa_add_new_table args p X aux = (case aux of ((t, pend, win, cc), ax) \<Rightarrow>
     (if memL (args_ivl args) 0
      then (case uag_step_ins p (args_n args) X cc ax of
              (cc', ax') \<Rightarrow> ((t, pend, append_queue (t, X) win, cc'), ax'))
      else ((t, append_queue (t, X) pend, win, cc), ax)))"
  by (simp add: usa_add_new_table_def uag_step_ins_def split: prod.splits)

lemma usa_expire_code[code]:
  "usa_expire args p nt win cc ax =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cc, ax)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cc, ax)
         else (case uag_step_del p (args_n args) (snd e) cc ax of
                 (cc', ax') \<Rightarrow> usa_expire args p nt (tl_queue win') cc' ax')))"
  by (subst usa_expire.simps) (simp add: uag_step_del_def split: prod.splits option.splits)
(*<*)
end
(*>*)
