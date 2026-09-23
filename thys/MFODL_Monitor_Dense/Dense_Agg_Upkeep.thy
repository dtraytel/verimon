(*<*)
theory Dense_Agg_Upkeep
  imports Dense_Agg_Code
begin
(*>*)

section \<open>The aggregation over a window, kept up in one pass per table\<close>

text \<open>
  When a time point's table enters the window of a fused aggregation (@{const usa_add_new_table})
  or leaves it (@{const usa_expire}), the node updates two structures: the count of every tuple in
  the window (@{const ucnt_add}, @{const ucnt_del}), and the per-group aggregate, which sees only
  the tuples that newly enter or finally leave (@{const uag_ins}, @{const uag_del}).  As defined,
  the second filters the table's list by the counts before the first pass has changed them, and
  then folds over what is left: two passes over the table, and every tuple's count read twice.

  The tuples of a table are distinct, so each one's count can be read and updated in the same
  pass without seeing another tuple's update.  @{text cnt_ins_fold} and @{text cnt_del_fold} are
  that pass, and @{text uag_step_ins_code} and @{text uag_step_del_code} below say that they
  compute exactly the two structures the two passes did.
\<close>

subsection \<open>The counts and the aggregate, in one pass\<close>

definition cnt_ins_fold :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list list \<Rightarrow> ucnt \<Rightarrow> 'b \<Rightarrow>
    ucnt \<times> 'b" where
  "cnt_ins_fold F xs c b = fold (\<lambda>t (c, acc). case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, F t acc)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, acc)) xs (c, b)"

definition cnt_del_fold :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list list \<Rightarrow> ucnt \<Rightarrow> 'b \<Rightarrow>
    ucnt \<times> 'b" where
  "cnt_del_fold F xs c b = fold (\<lambda>t (c, acc). case Mapping.lookup c t of
       None \<Rightarrow> (c, acc)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, if k = 1 then F t acc else acc)
                 else (Mapping.update t (k - 1) c, acc))) xs (c, b)"

lemma lookup_ucnt_add1_other: "u \<noteq> t \<Longrightarrow> Mapping.lookup (ucnt_add1 t c) u = Mapping.lookup c u"
  by (simp add: ucnt_add1_def lookup_update' split: option.splits)

lemma lookup_ucnt_del1_other: "u \<noteq> t \<Longrightarrow> Mapping.lookup (ucnt_del1 t c) u = Mapping.lookup c u"
  by (simp add: ucnt_del1_def lookup_update' lookup_delete split: option.splits)

lemma fold_filter_if: "fold F (filter P xs) b = fold (\<lambda>t acc. if P t then F t acc else acc) xs b"
  by (induct xs arbitrary: b) simp_all

lemma cnt_ins_fold_eq:
  "distinct xs \<Longrightarrow> cnt_ins_fold F xs c b =
     (fold ucnt_add1 xs c, fold F (filter (\<lambda>t. Mapping.lookup c t = None) xs) b)"
proof (induct xs arbitrary: c b)
  case (Cons t xs)
  have same: "\<And>b'. fold (\<lambda>u acc. if Mapping.lookup (ucnt_add1 t c) u = None then F u acc else acc) xs b'
      = fold (\<lambda>u acc. if Mapping.lookup c u = None then F u acc else acc) xs b'"
    using Cons.prems by (intro fold_cong refl) (metis distinct.simps(2) lookup_ucnt_add1_other)
  show ?case
    using Cons same
    by (auto simp: cnt_ins_fold_def ucnt_add1_def fold_filter_if split: option.splits)
qed (simp add: cnt_ins_fold_def)

lemma cnt_del_fold_eq:
  "distinct xs \<Longrightarrow> cnt_del_fold F xs c b =
     (fold ucnt_del1 xs c, fold F (filter (\<lambda>t. Mapping.lookup c t = Some 1) xs) b)"
proof (induct xs arbitrary: c b)
  case (Cons t xs)
  have same: "\<And>b'. fold (\<lambda>u acc. if Mapping.lookup (ucnt_del1 t c) u = Some 1 then F u acc else acc) xs b'
      = fold (\<lambda>u acc. if Mapping.lookup c u = Some 1 then F u acc else acc) xs b'"
    using Cons.prems by (intro fold_cong refl) (metis distinct.simps(2) lookup_ucnt_del1_other)
  show ?case
    using Cons same
    by (auto simp: cnt_del_fold_def ucnt_del1_def fold_filter_if split: option.splits)
qed (simp add: cnt_del_fold_def)

lemma distinct_csl_edl: "distinct (csl (X :: event_data list set))"
proof (cases "finite X")
  case True
  then show ?thesis
    using Dense_Unbox.ID_ccompare_ed by (simp add: csl_finite) (subst csorted_list_of_set_split, auto)
qed (simp add: csl_infinite)

subsection \<open>The window's two steps, in one pass each\<close>

definition uag_step_ins :: "daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow> ugagg option \<Rightarrow>
    ucnt \<times> ugagg option" where
  "uag_step_ins p w X c ax = (ucnt_add X c, uag_ins p w X c ax)"

definition uag_step_del :: "daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow> ugagg option \<Rightarrow>
    ucnt \<times> ugagg option" where
  "uag_step_del p w X c ax = (ucnt_del X c, uag_del p w X c ax)"

lemma uag_step_ins_code[code]:
  "uag_step_ins p w X c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     cnt_ins_fold (gstep_ins k (umeval_trm f)) (csl X) c ax)"
  by (cases p) (simp add: uag_step_ins_def cnt_ins_fold_eq[OF distinct_csl_edl] ucnt_add_def
      uag_ins_def gins_def)

lemma uag_step_del_code[code]:
  "uag_step_del p w X c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     cnt_del_fold (gstep_del k (umeval_trm f)) (csl X) c ax)"
  by (cases p) (simp add: uag_step_del_def cnt_del_fold_eq[OF distinct_csl_edl] ucnt_del_def
      uag_del_def gdel_def)

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

subsection \<open>The steps at the short tuples\<close>

text \<open>The steps of @{theory MFODL_Monitor_Dense.Dense_Agg_Gen} are generic in the element
  type, and their generated code built the comparator of the key lists at every lookup; these are
  their copies at @{typ event_data}, whose mapping operations the specialised ones take over.\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("gi_cnt", "edl_gi_cnt", ["event_data"]),
   ("gd_cnt", "edl_gd_cnt", ["event_data"]),
   ("gi_sum", "edl_gi_sum", ["event_data"]),
   ("gd_sum", "edl_gd_sum", ["event_data"]),
   ("gi_rank", "edl_gi_rank", ["event_data"]),
   ("gd_rank", "edl_gd_rank", ["event_data"]),
   ("gstep_ins", "edl_gstep_ins", ["event_data"]),
   ("gstep_del", "edl_gstep_del", ["event_data"])]
  ["edl_dict_simps"]\<close>

(*<*)
end
(*>*)
