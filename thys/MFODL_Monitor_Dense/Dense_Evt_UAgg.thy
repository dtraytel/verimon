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

lemma ua_step_rel:
  assumes "ua_rel p (args_n args) a u" and "valid_uw args cur u auxlist"
    and "dagg_ok p (args_n args)" and "args_R args = {0..<args_n args}"
    and "fst a = (nts, win, rest, len, bend, cc, dn)" and "len \<noteq> 0"
  shows "ua_rel p (args_n args) (ua_step args p (args_n args) ts0 a) (uw_step args ts0 u)"
  sorry

lemma ua_shift_rel:
  assumes "ua_rel p (args_n args) a u" and "valid_uw args cur u auxlist" and "cur \<le> nt"
    and "dagg_ok p (args_n args)" and "args_R args = {0..<args_n args}"
  shows "ua_rel p (args_n args) (ua_shift args p (args_n args) nt a) (uw_shift args nt u)"
  sorry

lemma valid_ua_add_new:
  assumes v: "valid_ua args p cur a auxlist"
    and t1: "table (args_n args) {} rel1" and X: "(X = {}) = (rel1 = {})"
    and t2: "table (args_n args) (args_R args) rel2" and f2: "finite rel2"
    and inz: "memL (args_ivl args) 0" and cn: "cur \<le> nt"
  shows "valid_ua args p nt (ua_add_new args p (args_n args) X rel2 nt a)
           (update_until args rel1 rel2 nt auxlist)"
  sorry

lemma valid_ua_eval:
  assumes v: "valid_ua args p cur a auxlist" and cn: "cur \<le> nt"
    and ev: "ua_eval args p (args_n args) nt a = (res, a')"
    and eu: "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "valid_ua args p cur a' auxlist' \<and> res = map (dagg_p p) res'"
  sorry

(*<*)
end
(*>*)
