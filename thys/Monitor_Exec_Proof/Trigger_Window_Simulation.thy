(*<*)
theory Trigger_Window_Simulation
  imports "Monitor_Exec.Trigger_Window" Exec_Until_Simulation Release_Window_Simulation "Monitor_Impl_Proof.Monitor_Instance_Valid"
begin
(*>*)



lemma emsk_args_distinct_R: "emsk_args args msk \<Longrightarrow> distinct (args_R args)"
  by (simp add: emsk_args_def strict_sorted_iff)


lemma tok_mem0: "mem (args_ivl args) 0 \<Longrightarrow> tok cR cL args"
  by (simp add: tok_def)

subsection \<open>The read is a finite table\<close>

text \<open>The read of the trigger structure is a finite table over the right operand's columns.
  With an interval containing zero that is immediate, because the window then always holds the
  latest time point and the read is contained in its right table.  Without it a safe trigger has
  the same columns on both sides, and the read is contained in the union of the window's
  tables -- which is what the weakened form below states.\<close>

lemma ftable_trigger_results:
  fixes args :: args
  assumes wf: "\<forall>(t, l, r) \<in> set auxlist. ftable L l \<and> ftable R r"
    and ne: "auxlist \<noteq> []" and m0: "mem (args_ivl args) 0"
    and lst: "fst (last auxlist) = cur" and aR: "args_R args = R"
  shows "ftable R (snd (trigger_results args cur auxlist))"
    and "fst (trigger_results args cur auxlist) = R"
proof -
  have kl: "length auxlist - 1 < length auxlist" using ne by simp
  obtain l0 r0 where a0: "auxlist ! (length auxlist - 1) = (cur, l0, r0)"
    using lst ne by (cases "auxlist ! (length auxlist - 1)") (simp add: last_conv_nth)
  have mem0: "auxlist ! (length auxlist - 1) \<in> set auxlist" using kl by (rule nth_mem)
  have tr0: "ftable R r0" using wf mem0 a0 by force
  have mm: "mem (args_ivl args) (cur - cur)" using m0 by simp
  have m: "(cur, l0, r0) \<in> set auxlist" using mem0 a0 by simp
  have fl: "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist \<noteq> []"
  proof
    assume e: "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist = []"
    have "\<forall>x \<in> set auxlist. \<not> (case x of (t, _, _) \<Rightarrow> mem (args_ivl args) (cur - t))"
      using e unfolding filter_empty_conv by simp
    from this[rule_format, OF m] show False using mm by simp
  qed
  have tb: "table R (snd (trigger_results args cur auxlist))"
    using fl aR by (auto simp: table_def)
  have sub: "snd (trigger_results args cur auxlist) \<subseteq> r0"
  proof
    fix tu assume tu: "tu \<in> snd (trigger_results args cur auxlist)"
    have H: "\<forall>i \<in> {0..<length auxlist}. case auxlist ! i of (t, l, r) \<Rightarrow>
        mem (args_ivl args) (cur - t) \<longrightarrow>
        (tu \<in> r \<or> (\<exists>j \<in> {i<..<length auxlist}.
           join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
             (restrict (args_L args) (args_R args) tu)))"
      using tu fl by simp
    have "{length auxlist - 1<..<length auxlist} = {}" using ne by auto
    then show "tu \<in> r0" using H[rule_format, of "length auxlist - 1"] kl a0 mm by simp
  qed
  have fin: "finite (snd (trigger_results args cur auxlist))"
    by (rule finite_subset[OF sub]) (use tr0 in simp)
  show "ftable R (snd (trigger_results args cur auxlist))" using tb fin by simp
  show "fst (trigger_results args cur auxlist) = R" using fl aR by simp
qed

lemma ftable_trigger_results_weak:
  fixes args :: args
  assumes wf: "\<forall>(t, l, r) \<in> set auxlist. ftable L l \<and> ftable R r"
    and ne: "auxlist \<noteq> []" and lst: "fst (last auxlist) = cur"
    and aL: "args_L args = L" and aR: "args_R args = R" and dR: "distinct R"
    and wkc: "mem (args_ivl args) 0 \<or> (args_pos args \<and> set L = set R)"
  shows "ftable (fst (trigger_results args cur auxlist)) (snd (trigger_results args cur auxlist)) \<and>
    (fst (trigger_results args cur auxlist) = R \<or> fst (trigger_results args cur auxlist) = [])"
proof (cases "mem (args_ivl args) 0")
  case True
  show ?thesis using ftable_trigger_results[OF wf ne True lst aR] by simp
next
  case False
  then have pos: "args_pos args" and LR: "set L = set R" using wkc by auto
  show ?thesis
  proof (cases "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist = []")
    case True
    then show ?thesis by (simp add: table_def unit_table_def wf_tuple_def)
  next
    case False
    then obtain x where x: "x \<in> set auxlist"
      and px: "case x of (t, _, _) \<Rightarrow> mem (args_ivl args) (cur - t)"
      by (auto simp: filter_empty_conv)
    obtain t0 l0 r0 where x0: "x = (t0, l0, r0)" by (cases x)
    have mm: "mem (args_ivl args) (cur - t0)" using px x0 by simp
    obtain i0 where i0: "i0 < length auxlist" and xi: "auxlist ! i0 = (t0, l0, r0)"
      using x x0 by (auto simp: in_set_conv_nth)
    have fl: "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist)"
      using False by simp
    have tr0: "ftable R r0" using wf x x0 by force
    have tb: "table R (snd (trigger_results args cur auxlist))"
      using fl aR by (auto simp: table_def)
    have sub: "snd (trigger_results args cur auxlist)
        \<subseteq> r0 \<union> (\<Union>j \<in> {0..<length auxlist}. restrict R L ` (fst \<circ> snd) (auxlist ! j))"
    proof
      fix tu assume tu: "tu \<in> snd (trigger_results args cur auxlist)"
      have wt: "wf_tuple R tu" using tu fl aR by simp
      have pj: "restrict R L (restrict (args_L args) (args_R args) tu) = tu"
        using restrict_restrict[of R L R tu] restrict_idle[OF dR wt] aL aR LR by simp
      have H: "\<forall>i \<in> {0..<length auxlist}. case auxlist ! i of (t, l, r) \<Rightarrow>
          mem (args_ivl args) (cur - t) \<longrightarrow>
          (tu \<in> r \<or> (\<exists>j \<in> {i<..<length auxlist}.
             join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
               (restrict (args_L args) (args_R args) tu)))"
        using tu fl by simp
      have step: "tu \<in> r0 \<or> (\<exists>j \<in> {i0<..<length auxlist}.
          join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
            (restrict (args_L args) (args_R args) tu))"
        using H[rule_format, of i0] i0 xi mm by simp
      show "tu \<in> r0 \<union> (\<Union>j \<in> {0..<length auxlist}. restrict R L ` (fst \<circ> snd) (auxlist ! j))"
        using step pos by (auto intro: image_eqI[where f = "restrict R L", OF pj[symmetric]])
    qed
    have finl: "finite (\<Union>j \<in> {0..<length auxlist}. restrict R L ` (fst \<circ> snd) (auxlist ! j))"
    proof (rule finite_UN_I[OF finite_atLeastLessThan])
      fix j assume "j \<in> {0..<length auxlist}"
      then have m: "auxlist ! j \<in> set auxlist" by simp
      obtain vj lj rj where e: "auxlist ! j = (vj, lj, rj)" by (cases "auxlist ! j")
      show "finite (restrict R L ` (fst \<circ> snd) (auxlist ! j))" using wf m unfolding e by force
    qed
    have fin: "finite (snd (trigger_results args cur auxlist))"
      by (rule finite_subset[OF sub]) (use tr0 finl in simp)
    show ?thesis using tb fin fl aR by simp
  qed
qed

subsection \<open>The summaries\<close>

lemma sw_assoc_tcomp: "sw_assoc tcomp"
  by (simp add: sw_assoc_def tcomp_def ecomp_assoc)

lemma sw_assoc_Un: "sw_assoc (\<union>)"
  by (simp add: sw_assoc_def Un_assoc)

lemma sw_fold_Un: "sw_fold (\<union>) xs = (if xs = [] then None else Some (\<Union> (set xs)))"
  by (induct xs) (auto simp: sw_comp_def split: option.splits if_splits)

lemma tfold:
  "es \<noteq> [] \<Longrightarrow> sw_fold tcomp (map (\<lambda>(l, r). esum_of args msk l r) es) =
     Some ({x. tT args msk es x \<and> \<not> (\<exists>e \<in> set es. tphi args msk (fst e) x)},
           {x. tT args msk es x \<and> (\<exists>e \<in> set es. tphi args msk (fst e) x)})"
proof (induct es)
  case (Cons e es)
  obtain l r where e: "e = (l, r)" by (cases e)
  show ?case
  proof (cases "es = []")
    case True
    then show ?thesis
      by (auto simp: e sw_comp_def esum_of_eq esemi_def tphi_def)
  next
    case False
    then show ?thesis using Cons(1)
      by (auto simp: e sw_comp_def tcomp_def ecomp_alt esum_of_eq esemi_def tphi_def)
  qed
qed simp

lemma tT_last: "es \<noteq> [] \<Longrightarrow> tT args msk es x \<Longrightarrow> x \<in> snd (last es)"
proof (induct es)
  case (Cons e es) then show ?case by (cases e; cases "es = []") auto
qed simp

lemma tT_nth: "tT args msk es x \<longleftrightarrow> (\<forall>i < length es. x \<in> snd (es ! i) \<or>
     (\<exists>j < length es. i < j \<and> tphi args msk (fst (es ! j)) x))"
proof (induct es)
  case (Cons e es)
  obtain l r where ep: "e = (l, r)" by (cases e)
  have b: "(\<exists>e \<in> set es. tphi args msk (fst e) x) \<longleftrightarrow> (\<exists>j < length es. tphi args msk (fst (es ! j)) x)"
  proof
    assume "\<exists>e \<in> set es. tphi args msk (fst e) x"
    then obtain e' where e': "e' \<in> set es" "tphi args msk (fst e') x" by blast
    then obtain j where "j < length es" "es ! j = e'" by (auto simp: in_set_conv_nth)
    then show "\<exists>j < length es. tphi args msk (fst (es ! j)) x" using e'(2) by auto
  next
    assume "\<exists>j < length es. tphi args msk (fst (es ! j)) x"
    then show "\<exists>e \<in> set es. tphi args msk (fst e) x" using nth_mem by blast
  qed
  show ?case unfolding ep length_Cons All_less_Suc2 Ex_less_Suc2 nth_Cons_0 nth_Cons_Suc tT.simps
      Cons b by simp
qed simp

lemma memL_ts_anti: "t \<le> t' \<Longrightarrow> memL I (c - t') \<Longrightarrow> memL I (c - t)"
  by (erule memL_mono) simp

lemma not_memR_ts_anti: "t \<le> t' \<Longrightarrow> \<not> memR I (c - t') \<Longrightarrow> \<not> memR I (c - t)"
  by (meson diff_le_mono2 memR_antimono)

lemma trel_split:
  assumes s: "List.sorted (map fst D)"
  shows "D = filter (\<lambda>x. memL I (c - fst x)) D @ filter (\<lambda>x. \<not> memL I (c - fst x)) D"
  using sorted_takeWhile_filter[OF s, of "\<lambda>t. memL I (c - t)"] memL_ts_anti
  by (metis takeWhile_dropWhile_id)

lemma trel_init: "trel args msk 0 (tw_init args msk) []"
  by (simp add: trel_def tw_init_def sw_rel_empty)

lemma tw_push:
  "sw_rel tcomp id W X \<Longrightarrow> sw_rel tcomp id (tw_push args msk nt mv W)
     (X @ map (tent args msk) (filter (\<lambda>x. memR (args_ivl args) (nt - fst x)) mv))"
proof (induct mv arbitrary: W X)
  case (Cons y mv)
  obtain t l r where y: "y = (t, l, r)" by (cases y)
  show ?case
  proof (cases "memR (args_ivl args) (nt - t)")
    case True
    have "sw_rel tcomp id (sw_push tcomp id t (esum_of args msk l r) W) (X @ [tent args msk y])"
      unfolding y tent_def fst_conv snd_conv by (rule sw_rel_push[OF sw_assoc_tcomp Cons(2)])
    from Cons(1)[OF this] show ?thesis using True by (simp add: tw_push_def y)
  next
    case False
    then show ?thesis using Cons by (simp add: tw_push_def y)
  qed
qed (simp add: tw_push_def)

lemma trel_update:
  fixes D :: "(ts \<times> 'b list set \<times> 'b list set) list"
  assumes r: "trel args msk cur ax D" and nt: "cur \<le> nt"
  shows "trel args msk nt (tw_update args nt l r ax)
    (filter (\<lambda>x. memR (args_ivl args) (nt - fst x)) D @ [(nt, l, r)])"
proof -
  let ?I = "args_ivl args"
  define Lc where "Lc = (\<lambda>x :: ts \<times> 'b list set \<times> 'b list set. memL ?I (cur - fst x))"
  define Ln where "Ln = (\<lambda>x :: ts \<times> 'b list set \<times> 'b list set. memL ?I (nt - fst x))"
  define Rn where "Rn = (\<lambda>x :: ts \<times> 'b list set \<times> 'b list set. memR ?I (nt - fst x))"
  obtain P W where ax: "ax = (msk, P, W)" using r by (cases ax) (auto simp: trel_def)
  have s: "List.sorted (map fst D)" and le: "\<forall>x \<in> set D. fst x \<le> cur"
    and rc: "\<forall>x \<in> set D. memR ?I (cur - fst x)"
    and rP: "sw_rel (\<union>) fst P (filter (\<lambda>x. \<not> Lc x) D)"
    and rW: "sw_rel tcomp id W (map (tent args msk) (filter Lc D))"
    using r by (auto simp: trel_def ax Lc_def)
  define Wl where "Wl = filter Lc D"
  define Pl where "Pl = filter (\<lambda>x. \<not> Lc x) D"
  have D: "D = Wl @ Pl" unfolding Wl_def Pl_def Lc_def by (rule trel_split[OF s])
  have sW: "List.sorted (map fst Wl)" and sP: "List.sorted (map fst Pl)"
    using s by (simp_all add: Wl_def Pl_def sorted_filter)
  have LcLn: "Lc x \<Longrightarrow> Ln x" for x unfolding Lc_def Ln_def
    by (erule memL_mono) (use nt in simp)
  \<comment> \<open>the in-interval points that leave\<close>
  obtain ys W1 where p1: "sw_pop tcomp id (\<lambda>t. \<not> memR ?I (nt - t)) W = (ys, W1)" by (meson surj_pair)
  have "sw_rel tcomp id W1 (dropWhile (\<lambda>x. \<not> memR ?I (nt - fst x)) (map (tent args msk) Wl))"
    using sw_pop[OF rW[folded Wl_def] p1] by simp
  also have "dropWhile (\<lambda>x. \<not> memR ?I (nt - fst x)) (map (tent args msk) Wl)
      = map (tent args msk) (dropWhile (\<lambda>x. \<not> memR ?I (nt - fst x)) Wl)"
    by (simp add: dropWhile_map comp_def tent_def)
  also have "dropWhile (\<lambda>x. \<not> memR ?I (nt - fst x)) Wl = filter Rn Wl"
    using sorted_takeWhile_filter[OF sW, of "\<lambda>t. \<not> memR ?I (nt - t)"] not_memR_ts_anti
    by (simp add: Rn_def)
  finally have rW1: "sw_rel tcomp id W1 (map (tent args msk) (filter Rn Wl))" .
  have D': "filter (\<lambda>x. memR ?I (nt - fst x)) D @ [(nt, l, r)] = filter Rn D @ [(nt, l, r)]"
    by (simp add: Rn_def)
  have s': "List.sorted (map fst (filter Rn D @ [(nt, l, r)]))"
    using s le nt by (auto simp: sorted_append sorted_filter[where f = fst, unfolded comp_def])
  have b': "\<forall>x \<in> set (filter Rn D @ [(nt, l, r)]). fst x \<le> nt \<and> memR ?I (nt - fst x)"
    using le nt by (auto simp: Rn_def)
  show ?thesis
  proof (cases "mem ?I 0")
    case True
    then have L0: "memL ?I 0" by simp
    have allL: "memL ?I x" for x by (rule memL_mono[OF L0]) simp
    have Pl: "Pl = []" by (simp add: Pl_def Lc_def allL)
    have Wl: "Wl = D" by (simp add: Wl_def Lc_def allL)
    have u: "tw_update args nt l r ax = (msk, P, sw_push tcomp id nt (esum_of args msk l r) W1)"
      using True p1 by (simp add: tw_update_def ax Let_def)
    have "sw_rel tcomp id (sw_push tcomp id nt (esum_of args msk l r) W1)
        (map (tent args msk) (filter Rn D @ [(nt, l, r)]))"
      using sw_rel_push[OF sw_assoc_tcomp rW1, of nt "esum_of args msk l r"]
      by (simp add: Wl tent_def)
    then show ?thesis using rP Pl s' b' unfolding u D'
      by (simp add: trel_def allL Pl_def)
  next
    case False
    then have nL0: "\<not> memL ?I 0" by simp
    have nLn: "\<not> Ln (nt, l, r)" using nL0 by (simp add: Ln_def)
    have Rn_new: "Rn (nt, l, r)" by (simp add: Rn_def)
    have rP': "sw_rel (\<union>) fst (sw_push (\<union>) fst nt (l, r) P) (Pl @ [(nt, l, r)])"
      using sw_rel_push[OF sw_assoc_Un rP[folded Pl_def]] by simp
    obtain mv P' where p2: "sw_pop (\<union>) fst (\<lambda>t. memL ?I (nt - t)) (sw_push (\<union>) fst nt (l, r) P)
        = (mv, P')" by (meson surj_pair)
    have sPn: "List.sorted (map fst (Pl @ [(nt, l, r)]))"
      using sP le nt by (auto simp: sorted_append Pl_def)
    have tf: "takeWhile (\<lambda>x. memL ?I (nt - fst x)) (Pl @ [(nt, l, r)]) = filter Ln (Pl @ [(nt, l, r)])
        \<and> dropWhile (\<lambda>x. memL ?I (nt - fst x)) (Pl @ [(nt, l, r)]) = filter (\<lambda>x. \<not> Ln x) (Pl @ [(nt, l, r)])"
      using sorted_takeWhile_filter[OF sPn, of "\<lambda>t. memL ?I (nt - t)"] memL_ts_anti
      by (simp add: Ln_def)
    have mv: "mv = filter Ln Pl" and rP2: "sw_rel (\<union>) fst P' (filter (\<lambda>x. \<not> Ln x) Pl @ [(nt, l, r)])"
      using sw_pop[OF rP' p2] tf nLn by simp_all
    have u: "tw_update args nt l r ax = (msk, P', tw_push args msk nt mv W1)"
      using False p1 p2 by (simp add: tw_update_def ax Let_def)
    have rW2: "sw_rel tcomp id (tw_push args msk nt mv W1)
        (map (tent args msk) (filter Rn Wl @ filter Rn (filter Ln Pl)))"
      using tw_push[OF rW1, of args msk nt mv] by (simp add: mv Rn_def)
    have e1: "filter (\<lambda>x. \<not> Ln x) Pl = filter (\<lambda>x. \<not> Ln x) (filter Rn D)"
    proof -
      have "filter (\<lambda>x. \<not> Ln x) Pl = filter (\<lambda>x. \<not> Ln x) D"
        unfolding Pl_def filter_filter by (rule filter_cong) (auto dest: LcLn)
      also have "\<dots> = filter (\<lambda>x. \<not> Ln x) (filter Rn D)"
        unfolding filter_filter by (rule filter_cong)
          (auto simp: Ln_def Rn_def intro: not_memL_imp_memR[of "args_ivl args", simplified])
      finally show ?thesis .
    qed
    have e2: "filter Ln (filter Rn D) = filter Rn Wl @ filter Rn (filter Ln Pl)"
    proof -
      have "filter Ln (filter Rn D) = filter (\<lambda>x. Rn x \<and> Ln x) Wl @ filter (\<lambda>x. Rn x \<and> Ln x) Pl"
        by (subst D) (simp add: filter_filter conj_commute)
      moreover have "filter (\<lambda>x. Rn x \<and> Ln x) Wl = filter Rn Wl"
        by (rule filter_cong) (auto simp: Wl_def dest: LcLn)
      ultimately show ?thesis by (simp add: filter_filter conj_commute)
    qed
    have fn: "filter (\<lambda>x. \<not> memL ?I (nt - fst x)) (filter Rn D @ [(nt, l, r)])
        = filter (\<lambda>x. \<not> Ln x) Pl @ [(nt, l, r)]"
      using e1 nLn by (simp add: Ln_def)
    have fm: "filter (\<lambda>x. memL ?I (nt - fst x)) (filter Rn D @ [(nt, l, r)])
        = filter Rn Wl @ filter Rn (filter Ln Pl)"
      using e2 nLn by (simp add: Ln_def)
    show ?thesis unfolding u D' trel_def using s' b' rP2 rW2 fn fm by simp
  qed
qed

lemma trel_empty:
  assumes r: "trel args msk cur ax D"
  shows "tw_empty ax \<longleftrightarrow> filter (\<lambda>x. mem (args_ivl args) (cur - fst x)) D = []"
proof -
  have rc: "\<forall>x \<in> set D. memR (args_ivl args) (cur - fst x)"
    and rW: "sw_rel tcomp id (snd (snd ax))
       (map (tent args msk) (filter (\<lambda>x. memL (args_ivl args) (cur - fst x)) D))"
    using r by (auto simp: trel_def)
  show ?thesis unfolding tw_empty_def sw_null[OF rW] using rc
    by (auto simp: filter_empty_conv)
qed

lemma trel_result:
  assumes r: "trel args msk cur ax D" and ne: "\<not> tw_empty ax"
    and dm: "emsk_args args msk"
    and wf: "\<forall>x \<in> set D. table (args_L args) (fst (snd x)) \<and> table (args_R args) (snd (snd x))"
    and ok: "mem (args_ivl args) 0 \<or> (args_L args = args_R args \<and> args_pos args)"
  shows "tw_result ax = snd (trigger_results args cur D)"
proof -
  let ?I = "args_ivl args" and ?L = "args_L args" and ?R = "args_R args"
  define Lc where "Lc = (\<lambda>x :: ts \<times> event_data list set \<times> event_data list set. memL ?I (cur - fst x))"
  obtain P W where ax: "ax = (msk, P, W)" using r by (cases ax) (auto simp: trel_def)
  have s: "List.sorted (map fst D)" and rc: "\<forall>x \<in> set D. memR ?I (cur - fst x)"
    and rP: "sw_rel (\<union>) fst P (filter (\<lambda>x. \<not> Lc x) D)"
    and rW: "sw_rel tcomp id W (map (tent args msk) (filter Lc D))"
    using r by (auto simp: trel_def ax Lc_def)
  define Wl where "Wl = filter Lc D"
  define Pl where "Pl = filter (\<lambda>x. \<not> Lc x) D"
  have D: "D = Wl @ Pl" unfolding Wl_def Pl_def Lc_def by (rule trel_split[OF s])
  have Wne: "Wl \<noteq> []"
    using ne trel_empty[OF r] rc by (auto simp: Wl_def Lc_def filter_empty_conv)
  define es where "es = map snd Wl"
  have esne: "es \<noteq> []" using Wne by (simp add: es_def)
  have qW: "sw_query tcomp W = sw_fold tcomp (map (\<lambda>(l, r). esum_of args msk l r) es)"
    unfolding sw_query[OF sw_assoc_tcomp rW] Wl_def[symmetric] es_def
    by (simp add: tent_def comp_def case_prod_beta)
  have qP: "sw_query (\<union>) P = (if Pl = [] then None else Some (\<Union>x \<in> set Pl. fst (snd x)))"
    unfolding sw_query[OF sw_assoc_Un rP] Pl_def[symmetric] sw_fold_Un by (simp add: image_image)
  have res: "tw_result ax = {x. tT args msk es x} \<union> (\<Union>x \<in> set Pl. fst (snd x))"
    unfolding tw_result_def ax prod.case qW qP tfold[OF esne]
    by (auto simp: eunion_def)
  \<comment> \<open>the points of the window are the ones at the front\<close>
  have memi: "mem ?I (cur - fst (D ! i)) \<longleftrightarrow> i < length Wl" if "i < length D" for i
  proof -
    have "D ! i \<in> set D" using that by simp
    then have rr: "memR ?I (cur - fst (D ! i))" using rc by blast
    show ?thesis
    proof (cases "i < length Wl")
      case True
      then have "D ! i = Wl ! i" by (simp add: D nth_append)
      then have "Lc (D ! i)" using True nth_mem[OF True] by (simp add: Wl_def)
      then show ?thesis using rr True by (simp add: Lc_def)
    next
      case False
      then have "D ! i = Pl ! (i - length Wl)" "i - length Wl < length Pl"
        using that by (simp_all add: D nth_append)
      then have "\<not> Lc (D ! i)" using nth_mem[of "i - length Wl" Pl] by (auto simp: Pl_def)
      then show ?thesis using False by (simp add: Lc_def)
    qed
  qed
  have wfx: "length x = length ?R \<Longrightarrow> eproj msk x = restrict ?L ?R x" for x
    by (rule emsk_args_dproj[OF dm])
  have cond: "(\<forall>i < length D. mem ?I (cur - fst (D ! i)) \<longrightarrow>
         (x \<in> snd (snd (D ! i)) \<or>
          (\<exists>j. i < j \<and> j < length D \<and> join_cond (args_pos args) (fst (snd (D ! j))) (restrict ?L ?R x))))
      \<longleftrightarrow> tT args msk es x \<or> (\<exists>e \<in> set Pl. tphi args msk (fst (snd e)) x)"
    if wx: "wf_tuple ?R x" for x
  proof -
    have lx: "length x = length ?R" using wx by (simp add: wf_tuple_def)
    have jc: "join_cond (args_pos args) l (restrict ?L ?R x) \<longleftrightarrow> tphi args msk l x" for l
      by (simp add: join_cond_eq tphi_def wfx[OF lx])
    have DW: "D ! k = Wl ! k" if "k < length Wl" for k using that by (simp add: D nth_append)
    show ?thesis unfolding jc tT_nth
    proof (intro iffI)
      assume H: "\<forall>i < length D. mem ?I (cur - fst (D ! i)) \<longrightarrow>
          x \<in> snd (snd (D ! i)) \<or> (\<exists>j. i < j \<and> j < length D \<and> tphi args msk (fst (snd (D ! j))) x)"
      show "(\<forall>i<length es. x \<in> snd (es ! i) \<or> (\<exists>j<length es. i < j \<and> tphi args msk (fst (es ! j)) x)) \<or>
          (\<exists>e \<in> set Pl. tphi args msk (fst (snd e)) x)"
      proof (cases "\<exists>e \<in> set Pl. tphi args msk (fst (snd e)) x")
        case True then show ?thesis by blast
      next
        case nP: False
        have "\<forall>i<length es. x \<in> snd (es ! i) \<or> (\<exists>j<length es. i < j \<and> tphi args msk (fst (es ! j)) x)"
        proof (intro allI impI)
          fix i assume i: "i < length es"
          then have iW: "i < length Wl" by (simp add: es_def)
          then have iD: "i < length D" by (simp add: D)
          have Hi: "x \<in> snd (snd (D ! i)) \<or> (\<exists>j. i < j \<and> j < length D \<and> tphi args msk (fst (snd (D ! j))) x)"
            using H iD memi[OF iD] iW by blast
          show "x \<in> snd (es ! i) \<or> (\<exists>j<length es. i < j \<and> tphi args msk (fst (es ! j)) x)"
          proof (cases "x \<in> snd (snd (D ! i))")
            case True then show ?thesis using DW[OF iW] iW by (simp add: es_def)
          next
            case False
            then obtain j where j: "i < j" "j < length D" "tphi args msk (fst (snd (D ! j))) x"
              using Hi by blast
            show ?thesis
            proof (cases "j < length Wl")
              case True
              then show ?thesis using j DW[OF True] by (intro disjI2 exI[where x = j]) (simp add: es_def)
            next
              case False
              then have "D ! j = Pl ! (j - length Wl)" "j - length Wl < length Pl"
                using j by (simp_all add: D nth_append)
              then show ?thesis using nP j(3) nth_mem[of "j - length Wl" Pl] by auto
            qed
          qed
        qed
        then show ?thesis by blast
      qed
    next
      assume "(\<forall>i<length es. x \<in> snd (es ! i) \<or> (\<exists>j<length es. i < j \<and> tphi args msk (fst (es ! j)) x)) \<or>
          (\<exists>e \<in> set Pl. tphi args msk (fst (snd e)) x)"
      then show "\<forall>i < length D. mem ?I (cur - fst (D ! i)) \<longrightarrow>
          x \<in> snd (snd (D ! i)) \<or> (\<exists>j. i < j \<and> j < length D \<and> tphi args msk (fst (snd (D ! j))) x)"
      proof
        assume T: "\<forall>i<length es. x \<in> snd (es ! i) \<or> (\<exists>j<length es. i < j \<and> tphi args msk (fst (es ! j)) x)"
        show ?thesis
        proof (intro allI impI)
          fix i assume iD: "i < length D" and m: "mem ?I (cur - fst (D ! i))"
          have iW: "i < length Wl" using memi[OF iD] m by simp
          have "x \<in> snd (es ! i) \<or> (\<exists>j<length es. i < j \<and> tphi args msk (fst (es ! j)) x)"
            using T iW by (simp add: es_def)
          then show "x \<in> snd (snd (D ! i)) \<or> (\<exists>j. i < j \<and> j < length D \<and> tphi args msk (fst (snd (D ! j))) x)"
          proof
            assume "x \<in> snd (es ! i)" then show ?thesis using DW[OF iW] iW by (simp add: es_def)
          next
            assume "\<exists>j<length es. i < j \<and> tphi args msk (fst (es ! j)) x"
            then obtain j where j: "j < length Wl" "i < j" "tphi args msk (fst (snd (Wl ! j))) x"
              by (auto simp: es_def)
            then show ?thesis using DW[OF j(1)] by (intro disjI2 exI[where x = j]) (simp add: D)
          qed
        qed
      next
        assume "\<exists>e \<in> set Pl. tphi args msk (fst (snd e)) x"
        then obtain e where e: "e \<in> set Pl" "tphi args msk (fst (snd e)) x" by blast
        obtain k where k: "k < length Pl" "Pl ! k = e" using e(1) by (auto simp: in_set_conv_nth)
        have De: "D ! (length Wl + k) = e" "length Wl + k < length D" using k by (simp_all add: D)
        show ?thesis
        proof (intro allI impI)
          fix i assume iD: "i < length D" and m: "mem ?I (cur - fst (D ! i))"
          have iW: "i < length Wl" using memi[OF iD] m by simp
          show "x \<in> snd (snd (D ! i)) \<or> (\<exists>j. i < j \<and> j < length D \<and> tphi args msk (fst (snd (D ! j))) x)"
            using iW e(2) De by (intro disjI2 exI[where x = "length Wl + k"]) simp
        qed
      qed
    qed
  qed
  have fl: "0 < length (filter (\<lambda>(t, _, _). mem ?I (cur - t)) D)"
  proof -
    have "hd Wl \<in> set D" "Lc (hd Wl)" using Wne hd_in_set[OF Wne] by (auto simp: Wl_def)
    then have h: "hd Wl \<in> set D" "mem ?I (cur - fst (hd Wl))" using rc by (auto simp: Lc_def)
    then have "hd Wl \<in> set (filter (\<lambda>(t, _, _). mem ?I (cur - t)) D)" by (simp add: split_def)
    then show ?thesis by (rule length_pos_if_in_set)
  qed
  have tr: "snd (trigger_results args cur D) = {x. wf_tuple ?R x \<and>
      (tT args msk es x \<or> (\<exists>e \<in> set Pl. tphi args msk (fst (snd e)) x))}"
    unfolding trigger_results_eq if_P[OF fl] snd_conv
    by (intro Collect_cong conj_cong refl) (rule cond)
  \<comment> \<open>the window's part is within its last right table, the pending part within the left ones\<close>
  have lastW: "snd (last es) = snd (snd (last Wl))" using Wne by (simp add: es_def last_map)
  have lW: "last Wl \<in> set D" using Wne by (simp add: D)
  have tW: "tT args msk es x \<Longrightarrow> wf_tuple ?R x" for x
    using tT_last[OF esne, of args msk x] wf lW lastW by (auto simp: table_def)
  have pend: "{x. wf_tuple ?R x \<and> (\<exists>e \<in> set Pl. tphi args msk (fst (snd e)) x)}
      = (\<Union>x \<in> set Pl. fst (snd x))"
  proof (cases "Pl = []")
    case True then show ?thesis by simp
  next
    case False
    then obtain y where y: "y \<in> set Pl" by (cases Pl) auto
    then have "\<not> memL ?I (cur - fst y)" by (simp add: Pl_def Lc_def)
    then have "\<not> memL ?I 0" by (meson memL_mono zero_le)
    then have LR: "?L = ?R" and pos: "args_pos args" using ok by auto
    have dR: "distinct ?R" by (rule emsk_args_distinct_R[OF dm])
    have tp: "tphi args msk l x \<longleftrightarrow> x \<in> l" if "wf_tuple ?R x" for l x
      using that pos LR restrict_idle[OF dR that] wfx[of x]
      by (simp add: tphi_def wf_tuple_def)
    have tl: "\<forall>e \<in> set Pl. table ?R (fst (snd e))" using wf LR by (auto simp: D)
    show ?thesis using tp tl by (auto simp: table_def; force)
  qed
  show ?thesis unfolding res tr using tW pend by blast
qed

lemma etw_init: "etw kL cL kR cR args 0 (tw_init (eargs cR cL args) (emsk cR cL)) []"
  if "tok cR cL args"
  using that by (simp add: etw_def eauxlist3_def trel_init)

lemma etw_update:
  assumes v: "etw kL cL kR cR args cur daux auxlist" and nt: "cur \<le> nt"
    and tl: "table kL l" and tr: "table kR r"
  shows "etw kL cL kR cR args nt
      (tw_update (eargs cR cL args) nt (etabc kL cL l) (etabc kR cR r) daux)
      (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist @ [(nt, l, r)])"
proof -
  have w: "\<forall>(t, l, r) \<in> set auxlist. table kL l \<and> table kR r" and ok: "tok cR cL args"
    and d: "trel (eargs cR cL args) (emsk cR cL) cur daux (eauxlist3 kL cL kR cR auxlist)"
    using v by (auto simp: etw_def)
  have "trel (eargs cR cL args) (emsk cR cL) nt
      (tw_update (eargs cR cL args) nt (etabc kL cL l) (etabc kR cR r) daux)
      (filter (\<lambda>x. memR (args_ivl args) (nt - fst x)) (eauxlist3 kL cL kR cR auxlist)
       @ [(nt, etabc kL cL l, etabc kR cR r)])"
    using trel_update[OF d nt] by simp
  moreover have "eauxlist3 kL cL kR cR (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist @ [(nt, l, r)])
      = filter (\<lambda>x. memR (args_ivl args) (nt - fst x)) (eauxlist3 kL cL kR cR auxlist)
        @ [(nt, etabc kL cL l, etabc kR cR r)]"
    using eauxlist3_filter_append[where P = "\<lambda>t. memR (args_ivl args) (nt - t)" and kL = kL
        and cL = cL and kR = kR and cR = cR and auxlist = auxlist and nt = nt and l = l and r = r]
    by (simp add: split_def)
  ultimately show ?thesis using w tl tr ok by (auto simp: etw_def)
qed

lemma etw_window:
  assumes v: "etw kL cL kR cR args cur daux auxlist"
  shows "tw_empty daux \<longleftrightarrow> filter (\<lambda>(t, _). mem (args_ivl args) (cur - t)) auxlist = []"
proof -
  have d: "trel (eargs cR cL args) (emsk cR cL) cur daux (eauxlist3 kL cL kR cR auxlist)"
    using v by (simp add: etw_def)
  show ?thesis unfolding trel_empty[OF d]
    by (simp add: eauxlist3_def filter_empty_conv split_def)
qed

lemma etw_result:
  assumes v: "etw kL cL kR cR args cur daux auxlist" and ne: "\<not> tw_empty daux"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
  shows "tw_result daux = etabc kR cR (snd (trigger_results args cur auxlist))"
proof -
  have w: "\<forall>(t, l, r) \<in> set auxlist. table kL l \<and> table kR r" and ok: "tok cR cL args"
    and d: "trel (eargs cR cL args) (emsk cR cL) cur daux (eauxlist3 kL cL kR cR auxlist)"
    using v by (auto simp: etw_def)
  have dm: "emsk_args (eargs cR cL args) (emsk cR cL)"
    unfolding emsk_def
    by (rule emsk_args_dargs[OF eframeD(2)[OF fR] eframeD(2)[OF fL] eframe_sub[OF fR fL sub]])
  have wf': "\<forall>x \<in> set (eauxlist3 kL cL kR cR auxlist).
      table (args_L (eargs cR cL args)) (fst (snd x)) \<and> table (args_R (eargs cR cL args)) (snd (snd x))"
    by (auto simp: eauxlist3_def table_etabc)
  have ok': "mem (args_ivl (eargs cR cL args)) 0 \<or>
      (args_L (eargs cR cL args) = args_R (eargs cR cL args) \<and> args_pos (eargs cR cL args))"
    using ok by (simp add: tok_def)
  have fl: "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist)"
    using etw_window[OF v] ne by (auto simp: split_def)
  have f1: "fst (trigger_results args cur auxlist) = kR" using fl aR by simp
  have f2: "fst (trigger_results (eargs cR cL args) cur (eauxlist3 kL cL kR cR auxlist)) = cR"
    using fl length_filter_eauxlist3[of "\<lambda>t. mem (args_ivl args) (cur - t)" kL cL kR cR auxlist]
    by simp
  have "tw_result daux = snd (trigger_results (eargs cR cL args) cur (eauxlist3 kL cL kR cR auxlist))"
    by (rule trel_result[OF d ne dm wf' ok'])
  also have "\<dots> = etabc kR cR (snd (trigger_results args cur auxlist))"
    using etabc_trigger_results(2)[OF fR fL sub aL aR w, of cur] unfolding f1 f2 .
  finally show ?thesis .
qed

lemma etw_result_empty:
  assumes v: "etw kL cL kR cR args cur daux auxlist" and e: "tw_empty daux"
  shows "trigger_results args cur auxlist = ([], unit_table)"
  using etw_window[OF v] e by (simp add: split_def)

lemma sw_null_push: "\<not> sw_null (sw_push f g t e s)"
  by (cases s) (simp add: sw_push_def sw_null_def split: list.splits)

lemma tw_update_not_empty:
  assumes m0: "mem (args_ivl args) 0"
  shows "\<not> tw_empty (tw_update args nt l r ax)"
  using m0 by (cases ax) (simp add: tw_update_def tw_empty_def Let_def sw_null_push)

(*<*)
end
(*>*)
