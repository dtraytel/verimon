(*<*)
theory Until_Agg_Proof
  imports "Monitor_Exec.Until_Agg" Since_Agg_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



subsection \<open>It tracks the plain window\<close>

text \<open>The fused operations differ from @{const uw_extend}, @{const uw_step} and
  @{const uw_shift} only in the extra component and in what is pushed onto the list of finished
  answers.  The first lemmas say so: everything but that list steps identically.\<close>

lemma ua_extend_proj:
  "(case ua_extend args p w ts0 win rest bend cc ax of (a, b, c, d, e) \<Rightarrow> (a, b, c, d))
   = uw_extend args ts0 win rest bend cc"
proof (induct args p w ts0 win rest bend cc ax rule: ua_extend.induct)
  case (1 args p w ts0 win rest bend cc ax)
  show ?case
    by (subst ua_extend.simps, subst uw_extend.simps)
       (use 1 in \<open>auto split: option.splits prod.splits\<close>)
qed

lemma ua_extend_fst4:
  assumes "ua_extend args p w ts0 win rest bend cc ax = (win', rest', bend', cc', ax')"
  shows "uw_extend args ts0 win rest bend cc = (win', rest', bend', cc')"
  using ua_extend_proj[of args p w ts0 win rest bend cc ax] unfolding assms by simp

text \<open>And the aggregate it carries stays valid for the union it is kept against: the scan's
  insertions are exactly @{const cnt_add}'s, so @{thm [source] ag_inv_ins} applies at each of
  them.  This mirrors @{thm [source] sa_move_rep} for the Since window's scan.\<close>

lemma ua_extend_rep:
  assumes "linearize rest = rl"
    and "ua_extend args p (args_n args) ts0 win rest bend cc ax = (win', rest', bend', cc', ax')"
  shows "cnt_rep f cc \<longrightarrow> eagg_ok p (args_n args) \<longrightarrow>
    (\<forall>e \<in> set rl. finite (fst (snd e)) \<and> ewf_table (args_n args) (fst (snd e))) \<longrightarrow>
    ewf_table (args_n args) (snd cc) \<longrightarrow> ag_inv p (args_n args) cc ax \<longrightarrow>
    ag_inv p (args_n args) cc' ax'"
  using assms
proof (induct rl arbitrary: rest win bend cc ax win' rest' bend' cc' ax' f)
  case Nil
  obtain ho rest0 where sh: "safe_hd rest = (ho, rest0)" by (cases "safe_hd rest")
  have hn: "ho = None" using safe_hd_rep[OF sh] Nil(1) by (auto split: option.splits)
  show ?case using Nil(2)
    by (subst (asm) ua_extend.simps) (auto simp: sh[unfolded hn] split: if_splits)
next
  case (Cons e rl)
  obtain ho rest0 where sh: "safe_hd rest = (ho, rest0)" by (cases "safe_hd rest")
  have l0: "linearize rest0 = e # rl" using safe_hd_rep[OF sh] Cons(2) by simp
  have ho: "ho = Some e" using safe_hd_rep[OF sh] l0 by (cases ho) auto
  have lt: "linearize (tl_queue rest0) = rl" by (simp add: tl_queue_rep l0)
  show ?case
  proof (cases bend)
    case False
    then show ?thesis using Cons(3) by (subst (asm) ua_extend.simps) auto
  next
    case b: True
    show ?thesis
    proof (cases "memR (args_ivl args) (fst e - ts0)")
      case False
      then show ?thesis using Cons(3) by (subst (asm) ua_extend.simps) (auto simp: sh ho b)
    next
      case r: True
      have rec: "ua_extend args p (args_n args) ts0 (append_queue e win) (tl_queue rest0)
          (snd (snd e)) (cnt_add (fst (snd e)) cc) (ag_ins p (args_n args) (fst (snd e)) cc ax)
          = (win', rest', bend', cc', ax')"
        using Cons(3) by (subst (asm) ua_extend.simps) (simp add: sh ho b r)
      note IH = Cons(1)[OF lt rec, of "\<lambda>x. if x \<in> fst (snd e) then f x + 1 else f x"]
      show ?thesis
      proof (intro impI)
        assume cr: "cnt_rep f cc" and ok: "eagg_ok p (args_n args)"
          and tb: "\<forall>e \<in> set (e # rl). finite (fst (snd e)) \<and> ewf_table (args_n args) (fst (snd e))"
          and S: "ewf_table (args_n args) (snd cc)"
          and inv: "ag_inv p (args_n args) cc ax"
        have fe: "finite (fst (snd e))" and de: "ewf_table (args_n args) (fst (snd e))"
          using tb by auto
        have cr': "cnt_rep (\<lambda>x. if x \<in> fst (snd e) then f x + 1 else f x) (cnt_add (fst (snd e)) cc)"
          using cnt_rep_add[OF cr fe] by simp
        have inv': "ag_inv p (args_n args) (cnt_add (fst (snd e)) cc)
            (ag_ins p (args_n args) (fst (snd e)) cc ax)"
          by (rule ag_inv_ins[OF cr fe ok de S inv])
        have S': "ewf_table (args_n args) (snd (cnt_add (fst (snd e)) cc))"
          using cnt_rep_snd_add[OF cr fe] S de by auto
        show "ag_inv p (args_n args) cc' ax'"
          using IH cr' ok tb S' inv' by auto
      qed
    qed
  qed
qed

lemma valid_ua_init:
  assumes "length (args_R args) = args_n args" and "eagg_ok p (args_n args)"
  shows "valid_ua args p 0 (ua_init args p) []"
  using assms valid_uw_init[of args] ag_inv_init[of p "args_n args"]
  by (auto simp: valid_ua_def ua_rel_def ua_init_def uw_init_def)

text \<open>The two recursions in step, and the shift that drives them, keep the relation.\<close>

text \<open>What the plain window's validity gives about the tables it holds, in the form
  @{thm [source] ag_inv_ins} and @{thm [source] ag_inv_del} want them.\<close>

lemma valid_uw_tables:
  assumes v: "valid_uw args cur (nts, win, rest, len, bend, cc, dn) auxlist"
    and R: "length (args_R args) = args_n args"
  shows "\<forall>e \<in> set (linearize win @ linearize rest).
           finite (fst (snd e)) \<and> ewf_table (args_n args) (fst (snd e))"
    and "cnt_inv (map (fst \<circ> snd) (linearize win)) cc"
proof -
  have wf: "\<forall>e \<in> set (linearize win @ linearize rest).
      table (args_R args) (fst (snd e)) \<and> finite (fst (snd e))"
    using v by (auto simp: valid_uw_def Let_def)
  then show "\<forall>e \<in> set (linearize win @ linearize rest).
      finite (fst (snd e)) \<and> ewf_table (args_n args) (fst (snd e))"
    using R by (auto simp: table_def wf_tuple_def)
  show "cnt_inv (map (fst \<circ> snd) (linearize win)) cc"
    using v by (auto simp: valid_uw_def Let_def)
qed

text \<open>The step needs only what @{thm [source] valid_uw_tables} extracts, not the whole of
  @{const valid_uw}: the shift below applies it to states whose queue of pending time stamps has
  already had its head taken off.\<close>

lemma ua_step_rel:
  assumes rel: "ua_rel p (args_n args) a u"
    and u: "u = (nts, win, rest, len, bend, cc, dn)"
    and tbw: "\<forall>e \<in> set (linearize win @ linearize rest).
                finite (fst (snd e)) \<and> ewf_table (args_n args) (fst (snd e))"
    and cnt: "cnt_inv (map (fst \<circ> snd) (linearize win)) cc"
    and ok: "eagg_ok p (args_n args)" and R: "length (args_R args) = args_n args"
  shows "ua_rel p (args_n args) (ua_step args p (args_n args) ts0 a) (uw_step args ts0 u)"
proof -
  let ?n = "args_n args"
  obtain ax where a: "a = ((nts, win, rest, len, bend, cc, map (eagg_p p) dn), ax)"
    and inv: "ag_inv p ?n cc ax"
    using rel by (auto simp: ua_rel_def u split: prod.splits)
  note tb = tbw cnt
  obtain win1 rest1 bend1 cc1 ax1 where
    aext: "ua_extend args p ?n ts0 win rest bend cc ax = (win1, rest1, bend1, cc1, ax1)"
    by (cases "ua_extend args p ?n ts0 win rest bend cc ax") auto
  have ext: "uw_extend args ts0 win rest bend cc = (win1, rest1, bend1, cc1)"
    by (rule ua_extend_fst4[OF aext])
  define ex1 where "ex1 = uw_ext (args_ivl args) ts0 bend (linearize rest)"
  have w1: "linearize win1 = linearize win @ ex1"
    and c1: "cc1 = fold cnt_add (map (fst \<circ> snd) ex1) cc"
    using uw_extend_rep[OF refl ext] unfolding ex1_def by blast+
  have sub1: "set ex1 \<subseteq> set (linearize rest)"
    using uw_ext_prefix[of "linearize rest" "args_ivl args" ts0 bend] unfolding ex1_def
    by (metis Un_iff set_append subsetI)
  have tb1: "\<forall>e \<in> set (linearize win1). finite (fst (snd e)) \<and> ewf_table ?n (fst (snd e))"
    using tb(1) sub1 unfolding w1 by auto
  have cnt1: "cnt_inv (map (fst \<circ> snd) (linearize win1)) cc1"
  proof -
    have fm: "\<forall>T \<in> set (map (fst \<circ> snd) ex1). finite T" using tb(1) sub1 by auto
    show ?thesis unfolding w1 c1 using cnt_inv_adds[OF tb(2) fm] by simp
  qed
  have S1: "ewf_table ?n (snd cc1)" using cnt_inv_set[OF cnt1] tb1 by auto
  have inv1: "ag_inv p ?n cc1 ax1"
    using ua_extend_rep[OF refl aext, of "cnt_of (map (fst \<circ> snd) (linearize win))"]
      tb(1) tb(2) ok cnt_inv_set[OF tb(2)] inv by auto
  have res1: "ag_res p ?n cc1 ax1 = eagg_p p (snd cc1)"
    by (rule ag_res_inv[OF inv1 ok S1])
  show ?thesis
  proof (cases "safe_hd win1")
    case (Pair ho win')
    show ?thesis
    proof (cases ho)
      case None
      then have "linearize win1 = []" using safe_hd_rep[OF Pair] by (auto split: option.splits)
      then have e: "snd cc1 = {}" using cnt_inv_set[OF cnt1] by simp
      show ?thesis
        using inv1 res1 e
        by (simp add: ua_rel_def ua_step_def uw_step_def a u aext ext Pair None)
    next
      case (Some e)
      have ne: "linearize win1 \<noteq> []" and hd: "e = hd (linearize win1)"
        using safe_hd_rep[OF Pair] Some by auto
      have mem: "e \<in> set (linearize win1)" unfolding hd by (rule hd_in_set[OF ne])
      have fe: "finite (fst (snd e))" and de: "ewf_table ?n (fst (snd e))"
        using tb1 mem by auto
      have inv2: "ag_inv p ?n (cnt_del (fst (snd e)) cc1) (ag_del p ?n (fst (snd e)) cc1 ax1)"
        by (rule ag_inv_del[OF cnt1 fe ok de S1 inv1])
      show ?thesis
        using inv2 res1
        by (simp add: ua_rel_def ua_step_def uw_step_def Let_def a u aext ext Pair Some)
    qed
  qed
qed

lemma ua_shift_rel_gen:
  "w = args_n args \<Longrightarrow> ua_rel p w a u \<Longrightarrow> valid_uw args cur u auxlist \<Longrightarrow> cur \<le> nt \<Longrightarrow>
   eagg_ok p w \<Longrightarrow> length (args_R args) = w \<Longrightarrow>
   ua_rel p w (ua_shift args p w nt a) (uw_shift args nt u)"
proof (induct args p w nt a arbitrary: u cur auxlist rule: ua_shift.induct)
  case (1 args p w nt a)
  obtain nts win rest len bend cc dn where u: "u = (nts, win, rest, len, bend, cc, dn)"
    by (cases u) auto
  obtain ax where a: "a = ((nts, win, rest, len, bend, cc, map (eagg_p p) dn), ax)"
    and inv: "ag_inv p w cc ax"
    using 1(3) by (auto simp: ua_rel_def u split: prod.splits)
  note W = 1(2)
  obtain ho nts' where sh: "safe_hd nts = (ho, nts')" by (cases "safe_hd nts")
  show ?case
  proof (cases ho)
    case None
    then show ?thesis
      using inv
      by (subst ua_shift.simps, subst uw_shift.simps) (simp add: ua_rel_def a u sh)
  next
    case (Some ts0)
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - ts0) \<or> len = 0")
      case True
      then show ?thesis
        using inv
        by (subst ua_shift.simps, subst uw_shift.simps) (simp add: ua_rel_def a u sh Some)
    next
      case f: False
      let ?u' = "(nts', win, rest, len, bend, cc, dn)"
      let ?a' = "((nts', win, rest, len, bend, cc, map (eagg_p p) dn), ax)"
      have rel': "ua_rel p w ?a' ?u'" using inv by (simp add: ua_rel_def)
      note tb = valid_uw_tables[OF 1(4)[unfolded u] 1(7)[unfolded W]]
      have step: "ua_rel p w (ua_step args p w ts0 ?a') (uw_step args ts0 ?u')"
        unfolding W
        by (rule ua_step_rel[OF rel'[unfolded W] refl tb(1) tb(2) 1(6)[unfolded W] 1(7)[unfolded W]])
      have vstep: "valid_uw args nt (uw_step args ts0 ?u') auxlist"
        using valid_uw_step[OF 1(4)[unfolded u] refl _ sh[unfolded Some] _ 1(5)] f by auto
      have "ua_rel p w (ua_shift args p w nt (ua_step args p w ts0 ?a'))
              (uw_shift args nt (uw_step args ts0 ?u'))"
        by (rule 1(1)) (use u a sh Some f W step vstep 1(6) 1(7) in auto)
      then show ?thesis
        by (subst ua_shift.simps, subst uw_shift.simps) (simp add: a u sh Some f)
    qed
  qed
qed

lemma ua_shift_rel:
  assumes "ua_rel p (args_n args) a u" and "valid_uw args cur u auxlist" and "cur \<le> nt"
    and "eagg_ok p (args_n args)" and "length (args_R args) = args_n args"
  shows "ua_rel p (args_n args) (ua_shift args p (args_n args) nt a) (uw_shift args nt u)"
  by (rule ua_shift_rel_gen[OF refl assms])

text \<open>The two entry points.  Both shift first, and the relation is preserved by everything they
  do afterwards: appending to the queues touches neither the count set, nor the aggregate, nor
  the finished answers, and handing the answers over reverses a list the relation maps
  pointwise.\<close>

lemma valid_ua_add_new:
  assumes v: "valid_ua args p cur a auxlist" and L: "args_L args = []"
    and t1: "table [] rel1" and X: "(X = {}) = (rel1 = {})"
    and t2: "table (args_R args) rel2" and f2: "finite rel2"
    and inz: "memL (args_ivl args) 0" and cn: "cur \<le> nt"
  shows "valid_ua args p nt (ua_add_new args p (args_n args) X rel2 nt a)
           (update_until args rel1 rel2 nt auxlist)"
proof -
  let ?n = "args_n args"
  obtain u where rel: "ua_rel p ?n a u" and vu: "valid_uw args cur u auxlist"
    and R: "length (args_R args) = ?n" and ok: "eagg_ok p ?n"
    using v by (auto simp: valid_ua_def)
  have rs: "ua_rel p ?n (ua_shift args p ?n nt a) (uw_shift args nt u)"
    by (rule ua_shift_rel[OF rel vu cn ok R])
  obtain nts win rest len bend cc dn where s: "uw_shift args nt u = (nts, win, rest, len, bend, cc, dn)"
    by (cases "uw_shift args nt u") auto
  obtain ax where as: "ua_shift args p ?n nt a
      = ((nts, win, rest, len, bend, cc, map (eagg_p p) dn), ax)" and inv: "ag_inv p ?n cc ax"
    using rs by (auto simp: ua_rel_def s split: prod.splits)
  have "ua_rel p ?n (ua_add_new args p ?n X rel2 nt a) (uw_add_new args X rel2 nt u)"
    using inv by (simp add: ua_rel_def ua_add_new_def uw_add_new_def as s Let_def)
  then show ?thesis
    unfolding valid_ua_def
    using valid_uw_add_new[OF vu L t1 X t2 f2 inz cn] R ok by blast
qed

lemma valid_ua_eval:
  assumes v: "valid_ua args p cur a auxlist" and cn: "cur \<le> nt"
    and ev: "ua_eval args p (args_n args) nt a = (res, a')"
    and eu: "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "valid_ua args p cur a' auxlist' \<and> res = map (eagg_p p) res'"
proof -
  let ?n = "args_n args"
  obtain u where rel: "ua_rel p ?n a u" and vu: "valid_uw args cur u auxlist"
    and R: "length (args_R args) = ?n" and ok: "eagg_ok p ?n"
    using v by (auto simp: valid_ua_def)
  have rs: "ua_rel p ?n (ua_shift args p ?n nt a) (uw_shift args nt u)"
    by (rule ua_shift_rel[OF rel vu cn ok R])
  obtain nts win rest len bend cc dn where s: "uw_shift args nt u = (nts, win, rest, len, bend, cc, dn)"
    by (cases "uw_shift args nt u") auto
  obtain ax where as: "ua_shift args p ?n nt a
      = ((nts, win, rest, len, bend, cc, map (eagg_p p) dn), ax)" and inv: "ag_inv p ?n cc ax"
    using rs by (auto simp: ua_rel_def s split: prod.splits)
  obtain u' where uev: "uw_eval args nt u = (rev dn, u')"
    and u': "u' = (nts, win, rest, len, bend, cc, [])"
    by (simp add: uw_eval_def s)
  have aev: "ua_eval args p ?n nt a = (rev (map (eagg_p p) dn), ((nts, win, rest, len, bend, cc, []), ax))"
    by (simp add: ua_eval_def as)
  have vres: "valid_uw args cur u' auxlist' \<and> rev dn = res'"
    by (rule valid_uw_eval[OF vu cn uev eu])
  have rel': "ua_rel p ?n ((nts, win, rest, len, bend, cc, []), ax) u'"
    using inv by (simp add: ua_rel_def u')
  have a'eq: "a' = ((nts, win, rest, len, bend, cc, []), ax)"
    and reseq: "res = rev (map (eagg_p p) dn)"
    using ev[unfolded aev] by auto
  show ?thesis
  proof
    show "valid_ua args p cur a' auxlist'"
      unfolding valid_ua_def a'eq using rel' vres R ok by blast
    show "res = map (eagg_p p) res'" using vres unfolding reseq by (simp add: rev_map)
  qed
qed

lemma ua_extend_rua:
  "ua_extend args p w ts0 win rest bend (ucc cc) ax
   = (case uua_extend args p w ts0 win rest bend cc ax of
        (win', rest', bend', cc', ax') \<Rightarrow> (win', rest', bend', ucc cc', ax'))"
proof (induct args p w ts0 win rest bend cc ax rule: uua_extend.induct)
  case (1 args p w ts0 win rest bend cc ax)
  obtain h rest' where sh: "safe_hd rest = (h, rest')" by (cases "safe_hd rest")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst ua_extend.simps, subst uua_extend.simps) (simp add: sh)
  next
    case (Some e)
    note IH = 1[OF _ sh[symmetric] Some]
    show ?thesis
      by (subst ua_extend.simps, subst uua_extend.simps)
         (auto simp: sh Some IH split: prod.splits)
  qed
qed

lemma ua_step_rua: "ua_step args p w ts0 (rua a) = rua (uua_step args p w ts0 a)"
proof -
  obtain nts win rest len bend cc dn ax where a: "a = ((nts, win, rest, len, bend, cc, dn), ax)"
    by (cases a) auto
  obtain win' rest' bend' cc' ax' where
    e: "uua_extend args p w ts0 win rest bend cc ax = (win', rest', bend', cc', ax')"
    by (cases "uua_extend args p w ts0 win rest bend cc ax") auto
  obtain h win'' where sh: "safe_hd win' = (h, win'')" by (cases "safe_hd win'")
  show ?thesis
  proof (cases h)
    case None
    then show ?thesis
      unfolding a
      by (simp add: ua_step_def uua_step_def rua.simps uuwm.simps ua_extend_rua e sh)
  next
    case (Some x)
    obtain tx Xx bx where x: "x = (tx, Xx, bx)" by (metis prod_cases3)
    show ?thesis
      unfolding a
      by (simp add: ua_step_def uua_step_def rua.simps uuwm.simps ua_extend_rua e sh Some x Let_def)
  qed
qed

lemma ua_shift_rua: "ua_shift args p w nt (rua a) = rua (uua_shift args p w nt a)"
proof (induct args p w nt a rule: uua_shift.induct)
  case (1 args p w nt a)
  obtain nts win rest len bend cc dn ax where a: "a = ((nts, win, rest, len, bend, cc, dn), ax)"
    by (cases a) auto
  obtain h nts' where sh: "safe_hd nts = (h, nts')" by (cases "safe_hd nts")
  show ?case
  proof (cases h)
    case None
    then show ?thesis
      unfolding a
      by (subst ua_shift.simps, subst uua_shift.simps) (simp add: rua.simps uuwm.simps sh)
  next
    case (Some ts0)
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - ts0) \<or> len = 0")
      case True
      then show ?thesis
        unfolding a
        by (subst ua_shift.simps, subst uua_shift.simps) (simp add: rua.simps uuwm.simps sh Some)
    next
      case f: False
      have "ua_shift args p w nt (rua a)
          = ua_shift args p w nt (ua_step args p w ts0
              (rua ((nts', win, rest, len, bend, cc, dn), ax)))"
        unfolding a
        by (subst ua_shift.simps) (simp add: rua.simps uuwm.simps sh Some f)
      also have "\<dots> = ua_shift args p w nt
          (rua (uua_step args p w ts0 ((nts', win, rest, len, bend, cc, dn), ax)))"
        by (simp add: ua_step_rua)
      also have "\<dots> = rua (uua_shift args p w nt
          (uua_step args p w ts0 ((nts', win, rest, len, bend, cc, dn), ax)))"
        by (rule 1) (use a sh Some f in auto)
      also have "\<dots> = rua (uua_shift args p w nt a)"
        unfolding a by (subst (2) uua_shift.simps) (simp add: sh Some f)
      finally show ?thesis .
    qed
  qed
qed

lemma ua_add_new_rua:
  "ua_add_new args p w rel1 rel2 nt (rua a) = rua (uua_add_new args p w rel1 rel2 nt a)"
proof -
  obtain nts win rest len bend cc dn ax where s:
    "uua_shift args p w nt a = ((nts, win, rest, len, bend, cc, dn), ax)"
    by (cases "uua_shift args p w nt a") auto
  show ?thesis
    unfolding ua_add_new_def uua_add_new_def ua_shift_rua s
    by (simp add: rua.simps uuwm.simps Let_def)
qed

lemma ua_eval_rua:
  "ua_eval args p w nt (rua a) = (case uua_eval args p w nt a of (res, a') \<Rightarrow> (res, rua a'))"
proof -
  obtain nts win rest len bend cc dn ax where s:
    "uua_shift args p w nt a = ((nts, win, rest, len, bend, cc, dn), ax)"
    by (cases "uua_shift args p w nt a") auto
  show ?thesis
    using ua_shift_rua[of args p w nt a]
    by (simp add: ua_eval_def uua_eval_def rua.simps uuwm.simps s)
qed

end
(*>*)
