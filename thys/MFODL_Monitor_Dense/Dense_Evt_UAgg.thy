(*<*)
theory Dense_Evt_UAgg
  imports Dense_Evt_Agg
begin
(*>*)

section \<open>The Until window with the aggregation fused in\<close>

text \<open>
  @{theory MFODL_Monitor_Dense.Dense_Evt_Agg} fuses an aggregation into the Since window: the
  count set makes each tuple's entry into and exit from the window's union explicit, and those
  are exactly the events the kernel's incremental structure takes, so the aggregate is kept in
  step with the union and read off instead of recomputed.

  The Until window keeps a count set in the same way, but it differs in when its answers are
  produced: a time point's answer is settled only once the window has run far enough past it,
  so @{const uw_step} pushes a \<^emph>\<open>snapshot\<close> of the union onto a list of finished answers and
  @{const uw_eval} hands the list over later.  Fusing the aggregation therefore means two
  things: the aggregate is maintained alongside the count set through the same insertions
  (@{const uw_extend}) and deletions (@{const uw_step}), and what is pushed is the aggregate's
  own reading at that moment rather than the raw union.  The list of finished answers holds
  aggregated tables from then on, which is what makes this worth doing: the unfused node
  clusters every one of those tables into groups once per time point.
\<close>

subsection \<open>The structure\<close>

text \<open>The same seven components as @{typ uwaux}, paired with the kernel's incremental
  structure, exactly as @{typ swagg} pairs @{typ swaux} with it.  The list of finished answers
  inside holds tables the aggregation has already been applied to.\<close>

type_synonym uwagg = "uwaux \<times> aggaux option"

function ua_extend :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uw_entry queue \<Rightarrow> uw_entry queue \<Rightarrow> bool \<Rightarrow>
    cntset \<Rightarrow> aggaux option \<Rightarrow> uw_entry queue \<times> uw_entry queue \<times> bool \<times> cntset \<times> aggaux option" where
  "ua_extend args p w ts0 win rest bend cc ax =
     (if \<not> bend then (win, rest, bend, cc, ax)
      else (case safe_hd rest of
              (None, rest') \<Rightarrow> (win, rest', bend, cc, ax)
            | (Some e, rest') \<Rightarrow>
                (if memR (args_ivl args) (fst e - ts0)
                 then ua_extend args p w ts0 (append_queue e win) (tl_queue rest')
                        (snd (snd e)) (cnt_add (fst (snd e)) cc)
                        (ag_ins p w (fst (snd e)) cc ax)
                 else (win, rest', bend, cc, ax))))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, w, ts0, win, rest, bend, cc, ax). length (linearize rest))")
     (fastforce split: prod.splits)+

declare ua_extend.simps[simp del]

definition ua_init :: "args \<Rightarrow> daggp \<Rightarrow> uwagg" where
  "ua_init args p = (uw_init args, ag_init p (args_n args))"

definition ua_length :: "args \<Rightarrow> uwagg \<Rightarrow> nat" where
  "ua_length args a = uw_length args (fst a)"

definition ua_step :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uwagg \<Rightarrow> uwagg" where
  "ua_step args p w ts0 a = (case a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
     (case ua_extend args p w ts0 win rest bend cc ax of (win, rest, bend, cc, ax) \<Rightarrow>
        (case safe_hd win of
           (None, win') \<Rightarrow> ((tl_queue nts, win', rest, len - 1, bend, cc,
                             ag_res p w cc ax # dn), ax)
         | (Some e, win') \<Rightarrow>
           (let win'' = tl_queue win';
                r = ag_res p w cc ax;
                cc' = cnt_del (fst (snd e)) cc;
                ax' = ag_del p w (fst (snd e)) cc ax;
                bend' = (if Queue.is_empty win'' then True else bend)
            in ((tl_queue nts, win'', rest, len - 1, bend', cc', r # dn), ax')))))"

function ua_shift :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uwagg \<Rightarrow> uwagg" where
  "ua_shift args p w nt a = (case a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
     (case safe_hd nts of
        (None, nts') \<Rightarrow> ((nts', win, rest, len, bend, cc, dn), ax)
      | (Some ts0, nts') \<Rightarrow>
        (if memR (args_ivl args) (nt - ts0) \<or> len = 0
         then ((nts', win, rest, len, bend, cc, dn), ax)
         else ua_shift args p w nt (ua_step args p w ts0 ((nts', win, rest, len, bend, cc, dn), ax)))))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(args, p, w, nt, ((nts, win, rest, len, bend, cc, dn), ax)). len)")
     (auto simp: ua_step_def Let_def split: prod.splits option.splits)

declare ua_shift.simps[simp del]

definition ua_add_new :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow>
    uwagg \<Rightarrow> uwagg" where
  "ua_add_new args p w rel1 rel2 nt a =
     (case ua_shift args p w nt a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in ((append_queue nt nts, win, append_queue (nt, rel2, b) rest, len + 1, bend, cc, dn), ax)))"

definition ua_eval :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uwagg \<Rightarrow> event_data table list \<times> uwagg" where
  "ua_eval args p w nt a =
     (case ua_shift args p w nt a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
       (rev dn, ((nts, win, rest, len, bend, cc, []), ax)))"

subsection \<open>It tracks the plain window\<close>

text \<open>The fused operations differ from @{const uw_extend}, @{const uw_step} and
  @{const uw_shift} only in the extra component and in what is pushed onto the list of finished
  answers.  The first lemmas say so: everything but that list steps identically.\<close>

abbreviation ua_w :: "uwagg \<Rightarrow> uwaux" where
  "ua_w a \<equiv> fst a"

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
  shows "cnt_rep f cc \<longrightarrow> dagg_ok p (args_n args) \<longrightarrow>
    (\<forall>e \<in> set rl. finite (fst (snd e)) \<and> dwf_table (args_n args) (fst (snd e))) \<longrightarrow>
    dwf_table (args_n args) (snd cc) \<longrightarrow> ag_inv p (args_n args) cc ax \<longrightarrow>
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
        assume cr: "cnt_rep f cc" and ok: "dagg_ok p (args_n args)"
          and tb: "\<forall>e \<in> set (e # rl). finite (fst (snd e)) \<and> dwf_table (args_n args) (fst (snd e))"
          and S: "dwf_table (args_n args) (snd cc)"
          and inv: "ag_inv p (args_n args) cc ax"
        have fe: "finite (fst (snd e))" and de: "dwf_table (args_n args) (fst (snd e))"
          using tb by auto
        have cr': "cnt_rep (\<lambda>x. if x \<in> fst (snd e) then f x + 1 else f x) (cnt_add (fst (snd e)) cc)"
          using cnt_rep_add[OF cr fe] by simp
        have inv': "ag_inv p (args_n args) (cnt_add (fst (snd e)) cc)
            (ag_ins p (args_n args) (fst (snd e)) cc ax)"
          by (rule ag_inv_ins[OF cr fe ok de S inv])
        have S': "dwf_table (args_n args) (snd (cnt_add (fst (snd e)) cc))"
          using cnt_rep_snd_add[OF cr fe] S de by auto
        show "ag_inv p (args_n args) cc' ax'"
          using IH cr' ok tb S' inv' by auto
      qed
    qed
  qed
qed

subsection \<open>What it is valid for\<close>

text \<open>The fused window is related to a plain one that has taken the same steps: the same seven
  components, except that its finished answers are the plain window's with the aggregation
  applied, and the incremental structure stands for the window's current union.\<close>

definition ua_rel :: "daggp \<Rightarrow> nat \<Rightarrow> uwagg \<Rightarrow> uwaux \<Rightarrow> bool" where
  "ua_rel p w a u \<longleftrightarrow>
     (case a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
      (case u of (nts', win', rest', len', bend', cc', dn') \<Rightarrow>
         nts = nts' \<and> win = win' \<and> rest = rest' \<and> len = len' \<and> bend = bend' \<and> cc = cc' \<and>
         dn = map (dagg_p p) dn' \<and> ag_inv p w cc ax))"

definition valid_ua :: "args \<Rightarrow> daggp \<Rightarrow> ts \<Rightarrow> uwagg \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_ua args p cur a auxlist \<longleftrightarrow>
     (\<exists>u. ua_rel p (args_n args) a u \<and> valid_uw args cur u auxlist) \<and>
     args_R args = {0..<args_n args} \<and> dagg_ok p (args_n args)"

lemma valid_ua_init:
  assumes "args_R args = {0..<args_n args}" and "dagg_ok p (args_n args)"
  shows "valid_ua args p 0 (ua_init args p) []"
  using assms valid_uw_init[of args] ag_inv_init[of p "args_n args"]
  by (auto simp: valid_ua_def ua_rel_def ua_init_def uw_init_def)

lemma ua_rel_w:
  assumes "ua_rel p w a u"
  shows "ua_w a = (case u of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
    (nts, win, rest, len, bend, cc, map (dagg_p p) dn))"
  using assms by (auto simp: ua_rel_def split: prod.splits)

lemma ua_rel_inv: "ua_rel p w a u \<Longrightarrow> ag_inv p w (fst (snd (snd (snd (snd (snd (ua_w a)))))) ) (snd a)"
  by (auto simp: ua_rel_def split: prod.splits)

lemma valid_ua_length:
  assumes "valid_ua args p cur a auxlist"
  shows "ua_length args a = length auxlist"
proof -
  obtain u where r: "ua_rel p (args_n args) a u" and v: "valid_uw args cur u auxlist"
    using assms by (auto simp: valid_ua_def)
  show ?thesis
    using valid_uw_length[OF v] ua_rel_w[OF r]
    by (auto simp: ua_length_def uw_length_def split: prod.splits)
qed

text \<open>The two recursions in step, and the shift that drives them, keep the relation.\<close>

text \<open>What the plain window's validity gives about the tables it holds, in the form
  @{thm [source] ag_inv_ins} and @{thm [source] ag_inv_del} want them.\<close>

lemma valid_uw_tables:
  assumes v: "valid_uw args cur (nts, win, rest, len, bend, cc, dn) auxlist"
    and R: "args_R args = {0..<args_n args}"
  shows "\<forall>e \<in> set (linearize win @ linearize rest).
           finite (fst (snd e)) \<and> dwf_table (args_n args) (fst (snd e))"
    and "cnt_inv (map (fst \<circ> snd) (linearize win)) cc"
proof -
  have wf: "\<forall>e \<in> set (linearize win @ linearize rest).
      table (args_n args) (args_R args) (fst (snd e)) \<and> finite (fst (snd e))"
    using v by (auto simp: valid_uw_def Let_def)
  then show "\<forall>e \<in> set (linearize win @ linearize rest).
      finite (fst (snd e)) \<and> dwf_table (args_n args) (fst (snd e))"
    unfolding R by (auto simp: table_def wf_tuple_dwf)
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
                finite (fst (snd e)) \<and> dwf_table (args_n args) (fst (snd e))"
    and cnt: "cnt_inv (map (fst \<circ> snd) (linearize win)) cc"
    and ok: "dagg_ok p (args_n args)" and R: "args_R args = {0..<args_n args}"
  shows "ua_rel p (args_n args) (ua_step args p (args_n args) ts0 a) (uw_step args ts0 u)"
proof -
  let ?n = "args_n args"
  obtain ax where a: "a = ((nts, win, rest, len, bend, cc, map (dagg_p p) dn), ax)"
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
  have tb1: "\<forall>e \<in> set (linearize win1). finite (fst (snd e)) \<and> dwf_table ?n (fst (snd e))"
    using tb(1) sub1 unfolding w1 by auto
  have cnt1: "cnt_inv (map (fst \<circ> snd) (linearize win1)) cc1"
  proof -
    have fm: "\<forall>T \<in> set (map (fst \<circ> snd) ex1). finite T" using tb(1) sub1 by auto
    show ?thesis unfolding w1 c1 using cnt_inv_adds[OF tb(2) fm] by simp
  qed
  have S1: "dwf_table ?n (snd cc1)" using cnt_inv_set[OF cnt1] tb1 by auto
  have inv1: "ag_inv p ?n cc1 ax1"
    using ua_extend_rep[OF refl aext, of "cnt_of (map (fst \<circ> snd) (linearize win))"]
      tb(1) tb(2) ok cnt_inv_set[OF tb(2)] inv by auto
  have res1: "ag_res p ?n cc1 ax1 = dagg_p p (snd cc1)"
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
      have fe: "finite (fst (snd e))" and de: "dwf_table ?n (fst (snd e))"
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
   dagg_ok p w \<Longrightarrow> args_R args = {0..<w} \<Longrightarrow>
   ua_rel p w (ua_shift args p w nt a) (uw_shift args nt u)"
proof (induct args p w nt a arbitrary: u cur auxlist rule: ua_shift.induct)
  case (1 args p w nt a)
  obtain nts win rest len bend cc dn where u: "u = (nts, win, rest, len, bend, cc, dn)"
    by (cases u) auto
  obtain ax where a: "a = ((nts, win, rest, len, bend, cc, map (dagg_p p) dn), ax)"
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
      let ?a' = "((nts', win, rest, len, bend, cc, map (dagg_p p) dn), ax)"
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
    and "dagg_ok p (args_n args)" and "args_R args = {0..<args_n args}"
  shows "ua_rel p (args_n args) (ua_shift args p (args_n args) nt a) (uw_shift args nt u)"
  by (rule ua_shift_rel_gen[OF refl assms])

text \<open>The two entry points.  Both shift first, and the relation is preserved by everything they
  do afterwards: appending to the queues touches neither the count set, nor the aggregate, nor
  the finished answers, and handing the answers over reverses a list the relation maps
  pointwise.\<close>

lemma valid_ua_add_new:
  assumes v: "valid_ua args p cur a auxlist"
    and t1: "table (args_n args) {} rel1" and X: "(X = {}) = (rel1 = {})"
    and t2: "table (args_n args) (args_R args) rel2" and f2: "finite rel2"
    and inz: "memL (args_ivl args) 0" and cn: "cur \<le> nt"
  shows "valid_ua args p nt (ua_add_new args p (args_n args) X rel2 nt a)
           (update_until args rel1 rel2 nt auxlist)"
proof -
  let ?n = "args_n args"
  obtain u where rel: "ua_rel p ?n a u" and vu: "valid_uw args cur u auxlist"
    and R: "args_R args = {0..<?n}" and ok: "dagg_ok p ?n"
    using v by (auto simp: valid_ua_def)
  have rs: "ua_rel p ?n (ua_shift args p ?n nt a) (uw_shift args nt u)"
    by (rule ua_shift_rel[OF rel vu cn ok R])
  obtain nts win rest len bend cc dn where s: "uw_shift args nt u = (nts, win, rest, len, bend, cc, dn)"
    by (cases "uw_shift args nt u") auto
  obtain ax where as: "ua_shift args p ?n nt a
      = ((nts, win, rest, len, bend, cc, map (dagg_p p) dn), ax)" and inv: "ag_inv p ?n cc ax"
    using rs by (auto simp: ua_rel_def s split: prod.splits)
  have "ua_rel p ?n (ua_add_new args p ?n X rel2 nt a) (uw_add_new args X rel2 nt u)"
    using inv by (simp add: ua_rel_def ua_add_new_def uw_add_new_def as s Let_def)
  then show ?thesis
    unfolding valid_ua_def
    using valid_uw_add_new[OF vu t1 X t2 f2 inz cn] R ok by blast
qed

lemma valid_ua_eval:
  assumes v: "valid_ua args p cur a auxlist" and cn: "cur \<le> nt"
    and ev: "ua_eval args p (args_n args) nt a = (res, a')"
    and eu: "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "valid_ua args p cur a' auxlist' \<and> res = map (dagg_p p) res'"
proof -
  let ?n = "args_n args"
  obtain u where rel: "ua_rel p ?n a u" and vu: "valid_uw args cur u auxlist"
    and R: "args_R args = {0..<?n}" and ok: "dagg_ok p ?n"
    using v by (auto simp: valid_ua_def)
  have rs: "ua_rel p ?n (ua_shift args p ?n nt a) (uw_shift args nt u)"
    by (rule ua_shift_rel[OF rel vu cn ok R])
  obtain nts win rest len bend cc dn where s: "uw_shift args nt u = (nts, win, rest, len, bend, cc, dn)"
    by (cases "uw_shift args nt u") auto
  obtain ax where as: "ua_shift args p ?n nt a
      = ((nts, win, rest, len, bend, cc, map (dagg_p p) dn), ax)" and inv: "ag_inv p ?n cc ax"
    using rs by (auto simp: ua_rel_def s split: prod.splits)
  obtain u' where uev: "uw_eval args nt u = (rev dn, u')"
    and u': "u' = (nts, win, rest, len, bend, cc, [])"
    by (simp add: uw_eval_def s)
  have aev: "ua_eval args p ?n nt a = (rev (map (dagg_p p) dn), ((nts, win, rest, len, bend, cc, []), ax))"
    by (simp add: ua_eval_def as)
  have vres: "valid_uw args cur u' auxlist' \<and> rev dn = res'"
    by (rule valid_uw_eval[OF vu cn uev eu])
  have rel': "ua_rel p ?n ((nts, win, rest, len, bend, cc, []), ax) u'"
    using inv by (simp add: ua_rel_def u')
  have a'eq: "a' = ((nts, win, rest, len, bend, cc, []), ax)"
    and reseq: "res = rev (map (dagg_p p) dn)"
    using ev[unfolded aev] by auto
  show ?thesis
  proof
    show "valid_ua args p cur a' auxlist'"
      unfolding valid_ua_def a'eq using rel' vres R ok by blast
    show "res = map (dagg_p p) res'" using vres unfolding reseq by (simp add: rev_map)
  qed
qed

(*<*)
end
(*>*)
