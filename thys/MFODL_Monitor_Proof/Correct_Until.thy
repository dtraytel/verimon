(*<*)
theory Correct_Until
  imports 
    Correct_Bin_Ops 
    Correct_Agg
    Correct_Envs
begin
(*>*)


subsection \<open> Until \<close>


subsubsection \<open> Invariants \<close>

text \<open>The left tables of the auxiliary state are over the columns of the left operand, the right
  tables over those of the right operand.\<close>

definition wf_until_auxlist :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> bool \<Rightarrow>
    ty Formula.formula \<Rightarrow> \<I> \<Rightarrow> ty Formula.formula \<Rightarrow> event_data muaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne \<longleftrightarrow>
    list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      qtable (Formula.fv_list \<phi>) (mem_restr R (Formula.fv_list \<phi>)) (\<lambda>v. if pos
          then (\<forall>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (val n (Formula.fv_list \<phi>) v) k \<phi>)
          else (\<exists>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (val n (Formula.fv_list \<phi>) v) k \<phi>)) r1 \<and>
      qtable (Formula.fv_list \<psi>) (mem_restr R (Formula.fv_list \<psi>)) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < ne + length auxlist \<and>
          mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) j \<psi> \<and>
          (\<forall>k\<in>{i..<j}. if pos then Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) k \<phi>
            else \<not> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) k \<phi>))) r2)
      auxlist [ne..<ne+length auxlist]"

definition (in muaux) wf_until_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> event_data list set \<Rightarrow> args \<Rightarrow>
  ty Formula.formula \<Rightarrow> ty Formula.formula \<Rightarrow> 'muaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_until_aux \<sigma> V R args \<phi> \<psi> aux ne \<longleftrightarrow> Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and>
    valid_aggargs (args_n args) (Formula.fv_list \<psi>) (args_agg args) \<and>
    (\<exists>cur auxlist. valid_muaux args cur aux auxlist \<and>
      cur = (if ne + length auxlist = 0 then 0 else \<tau> \<sigma> (ne + length auxlist - 1)) \<and>
      wf_until_auxlist \<sigma> V (args_n args) R (args_pos args) \<phi> (args_ivl args) \<psi> auxlist ne)"

lemma (in muaux) wf_until_aux_Nil: "Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' \<Longrightarrow>
  valid_aggargs n (Formula.fv_list \<psi>') agg \<Longrightarrow> 
  wf_until_aux \<sigma> V R (init_args I n (Formula.fv_list \<phi>') (Formula.fv_list \<psi>') b agg) \<phi>' \<psi>'
    (init_muaux (init_args I n (Formula.fv_list \<phi>') (Formula.fv_list \<psi>') b agg)) 0"
  unfolding wf_until_aux_def wf_until_auxlist_def
  by (auto simp: init_args_def intro!: exI[of _ "[]"] valid_init_muaux[unfolded init_args_def])

lemma length_update_until: "length (update_until args rel1 rel2 nt aux) = Suc (length aux)"
  unfolding update_until_def by simp

lemma wf_update_until_auxlist:
  assumes pre: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne"
    and qtable1: "sat_table \<sigma> V n R (Formula.fv_list \<phi>) (ne + length auxlist) \<phi> rel1"
    and qtable2: "sat_table \<sigma> V n R (Formula.fv_list \<psi>) (ne + length auxlist) \<psi> rel2"
    and fvi_subset: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_pos: "args_pos args = pos"
    and args_L: "args_L args = Formula.fv_list \<phi>"
    and args_R: "args_R args = Formula.fv_list \<psi>"
  shows "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> (update_until args rel1 rel2 (\<tau> \<sigma> (ne + length auxlist)) auxlist) ne"
  unfolding wf_until_auxlist_def length_update_until
  unfolding update_until_def list.rel_map add_Suc_right upt.simps eqTrueI[OF le_add1] if_True
proof (rule list_all2_appendI, unfold list.rel_map, goal_cases old new)
  case old
  let ?m = "ne + length auxlist"
  let ?\<phi>s = "Formula.fv_list \<phi>" and ?\<psi>s = "Formula.fv_list \<psi>"
  have sat_\<phi>: "Formula.sat \<sigma> V (val n ?\<phi>s (restrict ?\<phi>s ?\<psi>s x)) k \<phi> \<longleftrightarrow> Formula.sat \<sigma> V (val n ?\<psi>s x) k \<phi>" for x k
    by (rule sat_restrict) simp
  show ?case
  proof (rule list.rel_mono_strong[OF assms(1)[unfolded wf_until_auxlist_def]]; safe, goal_cases mono1 mono2)
    case (mono1 i X Y v)
    then have "v < ?m"
      by simp
    show ?case
    proof (cases pos)
      case True
      show ?thesis
        unfolding args_pos if_P[OF True]
        by (rule qtable_inter[OF mono1(3) qtable1]) (use True \<open>v < ?m\<close> in \<open>auto simp: less_Suc_eq\<close>)
    next
      case False
      show ?thesis
        unfolding args_pos if_not_P[OF False]
        by (rule qtable_union[OF mono1(3) qtable1]) (use False \<open>v < ?m\<close> in \<open>auto simp: less_Suc_eq\<close>)
    qed
  next
    case (mono2 i X Y v)
    show ?case
    proof (cases "mem I (\<tau> \<sigma> ?m - \<tau> \<sigma> v)")
      case True
      let ?Q = "\<lambda>x. Formula.sat \<sigma> V (val n ?\<psi>s x) ?m \<psi> \<and> (if pos
        then \<forall>k\<in>{v..<?m}. Formula.sat \<sigma> V (val n ?\<psi>s x) k \<phi>
        else \<forall>k\<in>{v..<?m}. \<not> Formula.sat \<sigma> V (val n ?\<psi>s x) k \<phi>)"
      have join: "qtable ?\<psi>s (mem_restr R ?\<psi>s) ?Q (join ?\<psi>s rel2 pos ?\<phi>s X)"
        by (rule qtable_join_sub[OF qtable2 mono2(3) distinct_fvi_list distinct_fvi_list])
          (use fvi_subset in \<open>auto simp: sat_\<phi>\<close>)
      show ?thesis
        unfolding args_ivl args_pos args_L args_R if_P[OF True]
        by (rule qtable_union[OF mono2(4) join])
          (use True mono2(2) in \<open>auto simp: less_Suc_eq intro: exI[of _ ?m]\<close>)    next
      case False
      show ?thesis
        unfolding args_ivl if_not_P[OF False]
        by (rule qtable_cong[OF mono2(4) refl]) (use False in \<open>auto simp: less_Suc_eq\<close>)
    qed
  qed
next
  case new
  then show ?case
    by (auto intro!: qtable_empty qtable1 qtable2[THEN qtable_cong] exI[of _ "ne + length auxlist"]
        simp: args_ivl args_n args_pos less_Suc_eq zero_enat_def[symmetric])
qed

lemma (in muaux) wf_update_until:
  assumes pre: "wf_until_aux \<sigma> V R args \<phi> \<psi> aux ne"
    and qtable1: "sat_table \<sigma> V n R (Formula.fv_list \<phi>) (ne + length_muaux args aux) \<phi> rel1"
    and qtable2: "sat_table \<sigma> V n R (Formula.fv_list \<psi>) (ne + length_muaux args aux) \<psi> rel2"
    and fvi_subset: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv_list \<phi>"
    and args_R: "args_R args = Formula.fv_list \<psi>"
    and args_pos: "args_pos args = pos"
  shows "wf_until_aux \<sigma> V R args \<phi> \<psi> (add_new_muaux args rel1 rel2 (\<tau> \<sigma> (ne + length_muaux args aux)) aux) ne \<and>
      length_muaux args (add_new_muaux args rel1 rel2 (\<tau> \<sigma> (ne + length_muaux args aux)) aux) = Suc (length_muaux args aux)"
proof -
  from pre obtain cur auxlist where valid_aux: "valid_muaux args cur aux auxlist" and
    cur: "cur = (if ne + length auxlist = 0 then 0 else \<tau> \<sigma> (ne + length auxlist - 1))" and
    pre_list: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne"
    unfolding wf_until_aux_def args_ivl args_n args_pos by auto
  have length_aux: "length_muaux args aux = length auxlist"
    using valid_length_muaux[OF valid_aux] .
  define nt where "nt \<equiv> \<tau> \<sigma> (ne + length_muaux args aux)"
  have nt_mono: "cur \<le> nt"
    unfolding cur nt_def length_aux by simp
  define auxlist' where "auxlist' \<equiv> update_until args rel1 rel2 (\<tau> \<sigma> (ne + length auxlist)) auxlist"
  have length_auxlist': "length auxlist' = Suc (length auxlist)"
    unfolding auxlist'_def by (auto simp add: length_update_until)
  have tab1: "table (args_L args) rel1"
    using qtable1 unfolding args_L by (auto simp add: qtable_def)
  have tab2: "table (args_R args) rel2"
    using qtable2 unfolding args_R by (auto simp add: qtable_def)
  have fv_sub: "fv \<phi> \<subseteq> fv \<psi>"
    using pre unfolding wf_until_aux_def by auto
  moreover have valid_add_new_auxlist: "valid_muaux args nt (add_new_muaux args rel1 rel2 nt aux) auxlist'"
    using valid_add_new_muaux[OF valid_aux tab1 tab2 nt_mono]
    unfolding auxlist'_def nt_def length_aux .
  moreover have "length_muaux args (add_new_muaux args rel1 rel2 nt aux) = Suc (length_muaux args aux)"
    using valid_length_muaux[OF valid_add_new_auxlist] unfolding length_auxlist' length_aux[symmetric] .
  moreover have "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist' ne"
    using wf_update_until_auxlist[OF pre_list qtable1[unfolded length_aux] qtable2[unfolded length_aux] fv_sub
        args_ivl args_n args_pos args_L args_R]
    unfolding auxlist'_def .
  moreover have "\<tau> \<sigma> (ne + length auxlist) = (if ne + length auxlist' = 0 then 0 else \<tau> \<sigma> (ne + length auxlist' - 1))"
    unfolding cur length_auxlist' by auto
  ultimately show ?thesis
    using pre
    unfolding wf_until_aux_def nt_def length_aux args_ivl args_n args_pos by fast
qed

lemma wf_until_aux_Cons: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> (a # aux) ne \<Longrightarrow>
  wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> aux (Suc ne)"
  unfolding wf_until_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc cong: if_cong)

lemma wf_until_aux_Cons1: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_until_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma wf_until_aux_Cons3: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow>
  qtable (Formula.fv_list \<psi>) (mem_restr R (Formula.fv_list \<psi>)) (\<lambda>v. (\<exists>j. ne \<le> j \<and> j < Suc (ne + length aux) \<and>
    mem I ((\<tau> \<sigma> j - \<tau> \<sigma> ne)) \<and> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) j \<psi> \<and>
    (\<forall>k\<in>{ne..<j}. if pos then Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) k \<phi>
      else \<not> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) k \<phi>))) a2"
  unfolding wf_until_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc)
definition "Untilp pos \<phi> I \<psi> \<equiv> Formula.Until (if pos then \<phi> else Formula.Neg \<phi>) I \<psi>"

lemma (in maux) update_until':
  "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux'' (Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
  Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs =
  Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
  Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs + length_muaux args aux'' =
  min (Progress.progress \<sigma> P' \<phi>''' (j + \<delta>)) (Progress.progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
  list_all2 (\<lambda>i. sat_table \<sigma> V (agg_n args) R' (args_cols args) i (packagg args (Untilp pos \<phi>'' I \<psi>'')))
    [Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<
     Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs] zs \<and>
  nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (Progress.progress \<sigma> P' \<phi>'' (j + \<delta>)) (Progress.progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
  if q1: "list_all2 (\<lambda>i. sat_table \<sigma> V n R (Formula.fv_list \<phi>'') i \<phi>'')
    [Progress.progress \<sigma> P \<phi>'' j..<Progress.progress \<sigma> P' \<phi>'' (j + \<delta>)] xs"
  and q2: "list_all2 (\<lambda>i. sat_table \<sigma> V n R (Formula.fv_list \<psi>'') i \<psi>'')
    [Progress.progress \<sigma> P \<psi>'' j..<Progress.progress \<sigma> P' \<psi>'' (j + \<delta>)] ys"
  and eq1: "mbuf2t_take (add_new_muaux args) aux (mbuf2_add xs ys buf) t (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) = (aux', buf', nt, nts')"
  and eq2: "eval_muaux args nt aux' = (zs, aux'')"
  and pos: "if args_pos args then \<phi>''' = \<phi>'' else \<phi>''' = Formula.Neg \<phi>''"
  and wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
  and fvi_sub: "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>''"
  and buf: "wf_mbuf2' \<sigma> P V j n R \<phi>'' \<psi>'' buf"
  and nts: "wf_ts \<sigma> P j \<phi>'' \<psi>'' nts"
  and aux: "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j)"
  and args_ivl: "args_ivl args = I"
  and args_n: "args_n args = n"
  and args_L: "args_L args = Formula.fv_list \<phi>''"
  and args_R: "args_R args = Formula.fv_list \<psi>''"
  and args_pos: "pos = args_pos args"
  and t: "t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))))"
  and nt0: "nt = lookahead_ts nts' nts (map (\<tau> \<sigma>) [j ..< j + \<delta>]) t"
  and length_aux: "progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j + length_muaux args aux = min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)"
  and nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
  and mr: "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
  and valid_aggargs: "valid_aggargs n (Formula.fv_list \<psi>'') (args_agg args)"
proof -
  note sat.simps[simp del] progress_simps[simp del]
  define ne where "ne \<equiv> progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j"
  have \<phi>''': "progress \<sigma> P \<phi>''' j = progress \<sigma> P \<phi>'' j"  "progress \<sigma> P' \<phi>''' j = progress \<sigma> P' \<phi>'' j" for j
    using pos by (simp_all add: progress.simps split: if_splits)
  have update1: "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux' (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j) \<and>
      ne + length_muaux args aux' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
    using q1 q2 nts_snoc length_aux aux fvi_sub 
    unfolding \<phi>'''
    by (elim mbuf2t_take_add_induct'[where j'="j + \<delta>", OF eq1 wf_envs_P_simps[OF wf_envs] buf])
      (auto simp: args_n args_L args_R ne_def wf_update_until split: option.splits)
  then obtain cur auxlist' where valid_aux': "valid_muaux args cur aux' auxlist'" and
    cur: "cur = (if ne + length auxlist' = 0 then 0 else \<tau> \<sigma> (ne + length auxlist' - 1))" and
    wf_auxlist': "wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist' (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j)"
    unfolding wf_until_aux_def ne_def args_ivl args_n args_pos by auto
  have length_aux': "length_muaux args aux' = length auxlist'"
    using valid_length_muaux[OF valid_aux'] .
  have nts': "wf_ts \<sigma> P' (j + \<delta>) \<phi>'' \<psi>'' nts'"
    using q1 q2 wf_envs nts_snoc
    unfolding wf_ts_def
    by (intro mbuf2t_take_eqD(2)[OF eq1]) (auto intro: wf_mbuf2_add buf[unfolded wf_mbuf2'_def])
  have nt: "nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
  proof -
    let ?m = "min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)"
    let ?m' = "min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
    from nts have nts_rel: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?m..<j] nts"
      unfolding wf_ts_def .
    from nts' have nts'_rel: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?m'..<j + \<delta>] nts'"
      unfolding wf_ts_def .
    show ?thesis
    proof (cases "nts' = []")
      case False
      with nts'_rel have "hd nts' = \<tau> \<sigma> ?m'" "?m' < j + \<delta>"
        by (rule list_all2_hdD)+
      then have "j + \<delta> \<noteq> 0" "min (j + \<delta> - 1) ?m' = ?m'"
        by linarith+
      with \<open>hd nts' = \<tau> \<sigma> ?m'\<close> False show ?thesis
        unfolding mbuf2t_take_nt[OF eq1] by (simp only: hd_append if_False if_not_P)
    next
      case True
      with nts'_rel have "j + \<delta> \<le> ?m'"
        by auto
      show ?thesis
      proof (cases "\<delta> = 0")
        case False
        with \<open>j + \<delta> \<le> ?m'\<close> have "j + \<delta> \<noteq> 0" "min (j + \<delta> - 1) ?m' = j + \<delta> - 1"
          by linarith+
        with False show ?thesis
          unfolding mbuf2t_take_nt[OF eq1] \<open>nts' = []\<close>
          by (simp only: if_not_P) (simp add: hd_append hd_rev last_map)
      next
        case True
        show ?thesis
        proof (cases "nts = []")
          case False
          with nts_rel have "last nts = \<tau> \<sigma> (j - 1)" "?m < j"
            by (rule list_all2_lastD list_all2_hdD(2))+
          with \<open>j + \<delta> \<le> ?m'\<close> \<open>\<delta> = 0\<close> have "j + \<delta> \<noteq> 0" "min (j + \<delta> - 1) ?m' = j - 1"
            by linarith+
          with False \<open>last nts = \<tau> \<sigma> (j - 1)\<close> \<open>\<delta> = 0\<close> show ?thesis
            unfolding mbuf2t_take_nt[OF eq1] \<open>nts' = []\<close>
            by (simp only: if_not_P) (simp add: hd_append hd_rev)
        next
          case True
          with nts_rel have "j \<le> ?m"
            by auto
          with \<open>j + \<delta> \<le> ?m'\<close> \<open>\<delta> = 0\<close> have "min (j - 1) ?m = j - 1" "min (j + \<delta> - 1) ?m' = j - 1"
            by linarith+
          with True \<open>\<delta> = 0\<close> show ?thesis
            unfolding mbuf2t_take_nt[OF eq1] \<open>nts' = []\<close> t
            by (simp only: add_0_right upt_conv_Nil[OF order.refl] list.map(1) rev.simps(1)
                append_Nil list.sel(1))
        qed
      qed
    qed
  qed
  define zs'' where "zs'' = fst (eval_until I nt auxlist')"
  define auxlist'' where "auxlist'' = snd (eval_until I nt auxlist')"
  have current_w_le: "cur \<le> nt"
  proof -
    let ?M = "min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
    have len: "ne + length auxlist' = ?M"
      using conjunct2[OF update1] unfolding length_aux' \<phi>''' .
    have "?M \<le> j + \<delta>"
      using wf_envs_progress_le(2)[OF wf_envs, of \<psi>''] by linarith
    show ?thesis
    proof (cases "?M = 0")
      case True
      then show ?thesis
        unfolding cur len by simp
    next
      case False
      with \<open>?M \<le> j + \<delta>\<close> have "j + \<delta> \<noteq> 0" "?M - 1 \<le> min (j + \<delta> - 1) ?M"
        by linarith+
      then show ?thesis
        unfolding cur len nt if_not_P[OF False] if_not_P[OF \<open>j + \<delta> \<noteq> 0\<close>]
        by (intro \<tau>_mono)
    qed
  qed
  have valid_aux'': "valid_muaux args cur aux'' auxlist''"
    using valid_eval_muaux[OF valid_aux' current_w_le eq2, of zs'' auxlist'']
    by (auto simp add: args_ivl zs''_def auxlist''_def)
  have length_aux'': "length_muaux args aux'' = length auxlist''"
    using valid_length_muaux[OF valid_aux''] .
  have eq2': "eval_until I nt auxlist' = (zs'', auxlist'')"
    by (auto simp: zs''_def auxlist''_def)
  have length_aux'_aux'': "length_muaux args aux' = length zs'' + length_muaux args aux''"
    using eval_until_length[OF eq2'] unfolding length_aux' length_aux'' .
  have "i \<le> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<Longrightarrow>
      wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist' i \<Longrightarrow>
      i + length auxlist' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<Longrightarrow>
      wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist'' (progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
        i + length zs'' = progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
        i + length zs'' + length auxlist'' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
        list_all2 (\<lambda>i. qtable (Formula.fv_list \<psi>'') (mem_restr R (Formula.fv_list \<psi>''))
          (\<lambda>v. Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) i (Untilp pos \<phi>'' I \<psi>'')))
          [i..<i + length zs''] zs''" for i
    using eq2'
  proof (induction auxlist' arbitrary: zs'' auxlist'' i)
    case Nil
    then show ?case
      by (auto dest!: antisym[OF progress_Until_le])
  next
    case (Cons a aux')
    obtain t a1 a2 where "a = (t, a1, a2)" by (cases a)
    from Cons.prems(2) have aux': "wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux' (Suc i)"
      by (rule wf_until_aux_Cons)
    from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
      unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons1)
    from Cons.prems(2) have 3: "qtable (Formula.fv_list \<psi>'') (mem_restr R (Formula.fv_list \<psi>'')) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) j \<psi>'' \<and>
        (\<forall>k\<in>{i..<j}. if pos then Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) k \<phi>'' else \<not> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) k \<phi>''))) a2"
      unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons3)
    from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' =
          min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
      by simp
    have prog_le: "i \<ge> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
      if "memR I (nt - t)"
      using that nts' unfolding wf_ts_def progress.simps nt
      by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv \<phi>'''
          intro!: cInf_lower \<tau>_mono diff_le_mono simp del: upt_Suc split: if_splits list.splits)
    have prog_Suc: "Suc i \<le> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
      if "\<not> memR I (nt - t)"
    proof -
      let ?X = "{i. \<forall>k. k < j + \<delta> \<and> k \<le> min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
      let ?min = "min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))"
      from that have "?X \<noteq> {}"
        by (auto simp: \<phi>''' intro!: exI[of _ "progress \<sigma> P' \<phi>'' (j + \<delta>)"])
      have "j + \<delta> \<noteq> 0"
        using Suc_i_aux' wf_envs_progress_le(2)[OF wf_envs, of \<psi>''] by linarith
      show ?thesis
        unfolding progress.simps
      proof (rule cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
        fix x
        assume "x \<in> ?X"
        show "Suc i \<le> x"
        proof (rule ccontr)
          assume "\<not> Suc i \<le> x"
          then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> i"
            by (intro \<tau>_mono) simp
          have "?min < j + \<delta>" "?min \<le> min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
            using \<open>j + \<delta> \<noteq> 0\<close> unfolding \<phi>''' by linarith+
          with \<open>x \<in> ?X\<close> have "memR I (\<tau> \<sigma> ?min - \<tau> \<sigma> x)"
            by blast
          then have "memR I (nt - t)"
            unfolding nt 1 if_not_P[OF \<open>j + \<delta> \<noteq> 0\<close>]
            by (rule memR_antimono) (rule diff_le_mono2[OF \<open>\<tau> \<sigma> x \<le> \<tau> \<sigma> i\<close>])
          with that show False
            by contradiction
        qed
      qed
    qed
    have *: "k < progress \<sigma> P' \<psi> (j + \<delta>)" if
      "\<not> memR I (nt - \<tau> \<sigma> i)"
      "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "\<psi> = \<psi>'' \<or> \<psi> = \<phi>''" for k \<psi>
      using that nts' unfolding wf_ts_def nt
      by (auto simp: list_all2_Cons2 upt_eq_Cons_conv
          simp del: upt_Suc split: list.splits if_splits
          elim!: contrapos_np[of _ "k < _"] intro!: diff_le_mono diff_le_mono2)
    show ?case
    proof (cases "memR I (nt - t)")
      case True
      with Cons.prems(4) have "zs'' = []" "auxlist'' = a # aux'"
        by (simp_all add: \<open>a = (t, a1, a2)\<close>)
      moreover from Cons.prems(1) prog_le[OF True]
      have "i = progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
        by (rule antisym)
      ultimately show ?thesis
        using Cons.prems(2,3) by simp
    next
      case False
      obtain xs aux'' where eq: "eval_until I nt aux' = (xs, aux'')"
        by (cases "eval_until I nt aux'")
      with False Cons.prems(4) have zs'': "zs'' = a2 # xs" and aux'': "auxlist'' = aux''"
        by (simp_all add: \<open>a = (t, a1, a2)\<close>)
      have j_lt: "k < Suc (i + length aux')" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
        using *[OF False[unfolded 1] that, of \<psi>''] *[OF False[unfolded 1] that, of \<phi>''] Suc_i_aux'
        by (simp add: \<phi>''')
      have "qtable (Formula.fv_list \<psi>'') (mem_restr R (Formula.fv_list \<psi>'')) (\<lambda>v. Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) i (Untilp pos \<phi>'' I \<psi>'')) a2"
        by (rule qtable_cong[OF 3 refl]) (cases pos; auto simp: Untilp_def sat.simps j_lt)
      with Cons.IH[OF prog_Suc[OF False] aux' Suc_i_aux' eq] show ?thesis
        unfolding zs'' aux'' by (clarsimp simp: upt_conv_Cons simp del: upt_Suc)
    qed
  qed
  note wf_aux'' = this[OF wf_envs_progress_mono[OF wf_envs]
      wf_auxlist' conjunct2[OF update1, unfolded ne_def length_aux']] 
  have zs_def: "zs = map (eval_args_agg args) zs''"
    using valid_eval_muaux[OF valid_aux' current_w_le eq2, of zs'' auxlist'']
    unfolding eval_args_agg_def
    by (auto simp add: args_ivl zs''_def auxlist''_def split: option.splits)
  have len_zs'': "length zs'' = length zs"
    by (auto simp: zs_def)
  have fv: "fv (Untilp pos \<phi>'' I \<psi>'') = fv \<psi>''"
    using fvi_sub
    by (auto simp: Untilp_def)
  have "list_all2 (\<lambda>i. qtable (Formula.fv_list \<psi>'') (mem_restr R (Formula.fv_list \<psi>''))
      (\<lambda>v. Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) i (Untilp pos \<phi>'' I \<psi>'')))
      [Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<
       Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)] zs''"
    using wf_aux''
    by auto
  then have list_all2_zs: "list_all2 (\<lambda>i. sat_table \<sigma> V (agg_n args) R' (args_cols args) i (packagg args (Untilp pos \<phi>'' I \<psi>'')))
      [Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<
       Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)] zs"
    unfolding zs_def list_all2_map2
  proof (rule list_all2_mono)
    fix i X
    assume "qtable (Formula.fv_list \<psi>'') (mem_restr R (Formula.fv_list \<psi>'')) (\<lambda>v. Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) i (Untilp pos \<phi>'' I \<psi>'')) X"
    then have "sat_table \<sigma> V (args_n args) R (args_R args) i (Untilp pos \<phi>'' I \<psi>'') X"
      by (simp add: args_n args_R)
    moreover have "valid_aggargs (args_n args) (args_R args) (args_agg args)"
      using valid_aggargs by (simp add: args_n args_R)
    moreover have "set (args_R args) = fv (Untilp pos \<phi>'' I \<psi>'')"
      by (simp add: args_R fv)
    ultimately show "sat_table \<sigma> V (agg_n args) R' (args_cols args) i (packagg args (Untilp pos \<phi>'' I \<psi>'')) (eval_args_agg args X)"
      by (rule qtable_eval_args_agg[OF _ mr])  qed
  have "progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length auxlist' =
      progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist''"
    using wf_aux'' valid_aux'' length_aux'_aux''
    by (auto simp add: ne_def length_aux' length_aux'')
  then have "cur =
      (if progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist'' = 0 then 0
      else \<tau> \<sigma> (progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist'' - 1))"
    unfolding cur ne_def by auto
  then show "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux'' (progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
      progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs = progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
      progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs + length_muaux args aux'' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
      list_all2 (\<lambda>i. sat_table \<sigma> V (agg_n args) R' (args_cols args) i (packagg args (Untilp pos \<phi>'' I \<psi>'')))
      [progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs] zs \<and>
      nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
    using aux wf_aux'' valid_aux'' fvi_sub list_all2_zs
    unfolding wf_until_aux_def length_aux'' args_ivl args_n args_pos nt len_zs''
    by (auto simp only: length_aux'')
qed

(*<*)
end
(*>*)