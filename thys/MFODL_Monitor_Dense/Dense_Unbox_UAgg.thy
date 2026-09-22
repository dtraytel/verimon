(*<*)
theory Dense_Unbox_UAgg
  imports Dense_Unbox_Eval Dense_Evt_UAgg
begin
(*>*)

section \<open>The fused Until window over the short tuples\<close>

text \<open>
  @{theory MFODL_Monitor_Dense.Dense_Evt_UAgg} fuses the aggregation into the Until window at
  the boxed tuples.  This is the same structure over the short ones, and its naturality: a
  relabelling of the element type, with the incremental structure carried along unchanged, since
  the aggregation already reads a short table through @{const uag_ins}, @{const uag_del} and
  @{const uag_res}.  There is no invariant here -- that stayed a level below, in
  @{const valid_ua}.
\<close>

type_synonym uuwagg = "uuwaux \<times> aggaux option"

function uua_extend :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uuw_entry queue \<Rightarrow> uuw_entry queue \<Rightarrow> bool \<Rightarrow>
    event_data gcntset \<Rightarrow> aggaux option \<Rightarrow>
    uuw_entry queue \<times> uuw_entry queue \<times> bool \<times> event_data gcntset \<times> aggaux option" where
  "uua_extend args p w ts0 win rest bend cc ax =
     (if \<not> bend then (win, rest, bend, cc, ax)
      else (case safe_hd rest of
              (None, rest') \<Rightarrow> (win, rest', bend, cc, ax)
            | (Some e, rest') \<Rightarrow>
                (if memR (args_ivl args) (fst e - ts0)
                 then uua_extend args p w ts0 (append_queue e win) (tl_queue rest')
                        (snd (snd e)) (gcnt_add (fst (snd e)) cc)
                        (uag_ins p w (fst (snd e)) cc ax)
                 else (win, rest', bend, cc, ax))))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, w, ts0, win, rest, bend, cc, ax). length (linearize rest))")
     (fastforce split: prod.splits)+

declare uua_extend.simps[simp del]

definition uua_init :: "args \<Rightarrow> daggp \<Rightarrow> uuwagg" where
  "uua_init args p = (uuw_init args, ag_init p (args_n args))"

definition uua_length :: "args \<Rightarrow> uuwagg \<Rightarrow> nat" where
  "uua_length args a = uuw_length args (fst a)"

definition uua_step :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uuwagg \<Rightarrow> uuwagg" where
  "uua_step args p w ts0 a = (case a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
     (case uua_extend args p w ts0 win rest bend cc ax of (win, rest, bend, cc, ax) \<Rightarrow>
        (case safe_hd win of
           (None, win') \<Rightarrow> ((tl_queue nts, win', rest, len - 1, bend, cc,
                             uag_res p w cc ax # dn), ax)
         | (Some e, win') \<Rightarrow>
           (let win'' = tl_queue win';
                r = uag_res p w cc ax;
                cc' = gcnt_del (fst (snd e)) cc;
                ax' = uag_del p w (fst (snd e)) cc ax;
                bend' = (if Queue.is_empty win'' then True else bend)
            in ((tl_queue nts, win'', rest, len - 1, bend', cc', r # dn), ax')))))"

function uua_shift :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uuwagg \<Rightarrow> uuwagg" where
  "uua_shift args p w nt a = (case a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
     (case safe_hd nts of
        (None, nts') \<Rightarrow> ((nts', win, rest, len, bend, cc, dn), ax)
      | (Some ts0, nts') \<Rightarrow>
        (if memR (args_ivl args) (nt - ts0) \<or> len = 0
         then ((nts', win, rest, len, bend, cc, dn), ax)
         else uua_shift args p w nt
                (uua_step args p w ts0 ((nts', win, rest, len, bend, cc, dn), ax)))))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(args, p, w, nt, ((nts, win, rest, len, bend, cc, dn), ax)). len)")
     (auto simp: uua_step_def Let_def split: prod.splits option.splits)

declare uua_shift.simps[simp del]

definition uua_add_new :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> event_data list set \<Rightarrow> ts \<Rightarrow>
    uuwagg \<Rightarrow> uuwagg" where
  "uua_add_new args p w rel1 rel2 nt a =
     (case uua_shift args p w nt a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in ((append_queue nt nts, win, append_queue (nt, rel2, b) rest, len + 1, bend, cc, dn), ax)))"

definition uua_eval :: "args \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uuwagg \<Rightarrow>
    event_data list set list \<times> uuwagg" where
  "uua_eval args p w nt a =
     (case uua_shift args p w nt a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
       (rev dn, ((nts, win, rest, len, bend, cc, []), ax)))"

subsection \<open>Its naturality\<close>

fun rua :: "uuwagg \<Rightarrow> uwagg" where
  "rua (w, ax) = (ruw w, ax)"

declare rua.simps[simp del]

lemma ua_extend_rua:
  "ua_extend args p w ts0 (rqe win) (rqe rest) bend (rcc cc) ax
   = (case uua_extend args p w ts0 win rest bend cc ax of
        (win', rest', bend', cc', ax') \<Rightarrow> (rqe win', rqe rest', bend', rcc cc', ax'))"
proof (induct args p w ts0 win rest bend cc ax rule: uua_extend.induct)
  case (1 args p w ts0 win rest bend cc ax)
  obtain h rest' where sh: "safe_hd rest = (h, rest')" by (cases "safe_hd rest")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst ua_extend.simps, subst uua_extend.simps) (simp add: sh)
  next
    case (Some e)
    obtain te Xe be where e: "e = (te, Xe, be)" by (metis prod_cases3)
    note IH = 1[OF _ sh[symmetric] Some, unfolded e, simplified]
    show ?thesis
      by (subst ua_extend.simps, subst uua_extend.simps)
         (auto simp: sh Some e IH split: prod.splits)
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
      by (simp add: ua_step_def uua_step_def rua.simps ruw.simps ua_extend_rua e sh)
  next
    case (Some x)
    obtain tx Xx bx where x: "x = (tx, Xx, bx)" by (metis prod_cases3)
    show ?thesis
      unfolding a
      by (simp add: ua_step_def uua_step_def rua.simps ruw.simps ua_extend_rua e sh Some x Let_def)
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
      by (subst ua_shift.simps, subst uua_shift.simps) (simp add: rua.simps ruw.simps sh)
  next
    case (Some ts0)
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - ts0) \<or> len = 0")
      case True
      then show ?thesis
        unfolding a
        by (subst ua_shift.simps, subst uua_shift.simps) (simp add: rua.simps ruw.simps sh Some)
    next
      case f: False
      have "ua_shift args p w nt (rua a)
          = ua_shift args p w nt (ua_step args p w ts0
              (rua ((nts', win, rest, len, bend, cc, dn), ax)))"
        unfolding a
        by (subst ua_shift.simps) (simp add: rua.simps ruw.simps sh Some f)
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
  "ua_add_new args p w (reopt_table rel1) (reopt_table rel2) nt (rua a)
   = rua (uua_add_new args p w rel1 rel2 nt a)"
proof -
  obtain nts win rest len bend cc dn ax where s:
    "uua_shift args p w nt a = ((nts, win, rest, len, bend, cc, dn), ax)"
    by (cases "uua_shift args p w nt a") auto
  show ?thesis
    unfolding ua_add_new_def uua_add_new_def ua_shift_rua s
    by (simp add: rua.simps ruw.simps Let_def)
qed

lemma ua_eval_rua:
  "ua_eval args p w nt (rua a)
   = (case uua_eval args p w nt a of (res, a') \<Rightarrow> (map reopt_table res, rua a'))"
proof -
  obtain nts win rest len bend cc dn ax where s:
    "uua_shift args p w nt a = ((nts, win, rest, len, bend, cc, dn), ax)"
    by (cases "uua_shift args p w nt a") auto
  show ?thesis
    using ua_shift_rua[of args p w nt a]
    by (simp add: ua_eval_def uua_eval_def rua.simps ruw.simps s rev_map)
qed

lemma rua_init: "rua (uua_init args p) = ua_init args p"
  by (simp add: rua.simps uua_init_def ua_init_def uuw_init_def uw_init_def ruw.simps
      empty_queue_rep rcc.simps)

(*<*)
end
(*>*)
