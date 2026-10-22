(*<*)
theory Until_Agg
  imports Since_Agg
begin
(*>*)



section \<open>The Until window with the aggregation fused in\<close>

text \<open>
  @{theory MFODL_Monitor_Exec.Since_Agg} fuses an aggregation into the Since window: the
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

type_synonym uwagg = "uwaux \<times> egagg option"

function ua_extend :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uw_entry queue \<Rightarrow> uw_entry queue \<Rightarrow> bool \<Rightarrow>
    cntset \<Rightarrow> egagg option \<Rightarrow> uw_entry queue \<times> uw_entry queue \<times> bool \<times> cntset \<times> egagg option" where
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

definition ua_init :: "args \<Rightarrow> eaggp \<Rightarrow> uwagg" where
  "ua_init args p = (uw_init args, ag_init p (args_n args))"

definition ua_step :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uwagg \<Rightarrow> uwagg" where
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

function ua_shift :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uwagg \<Rightarrow> uwagg" where
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

definition ua_add_new :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow>
    uwagg \<Rightarrow> uwagg" where
  "ua_add_new args p w rel1 rel2 nt a =
     (case ua_shift args p w nt a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in ((append_queue nt nts, win, append_queue (nt, rel2, b) rest, len + 1, bend, cc, dn), ax)))"

definition ua_eval :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uwagg \<Rightarrow> event_data table list \<times> uwagg" where
  "ua_eval args p w nt a =
     (case ua_shift args p w nt a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
       (rev dn, ((nts, win, rest, len, bend, cc, []), ax)))"

subsection \<open>What it is valid for\<close>

text \<open>The fused window is related to a plain one that has taken the same steps: the same seven
  components, except that its finished answers are the plain window's with the aggregation
  applied, and the incremental structure stands for the window's current union.\<close>

definition ua_rel :: "eaggp \<Rightarrow> nat \<Rightarrow> uwagg \<Rightarrow> uwaux \<Rightarrow> bool" where
  "ua_rel p w a u \<longleftrightarrow>
     (case a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
      (case u of (nts', win', rest', len', bend', cc', dn') \<Rightarrow>
         nts = nts' \<and> win = win' \<and> rest = rest' \<and> len = len' \<and> bend = bend' \<and> cc = cc' \<and>
         dn = map (eagg_p p) dn' \<and> ag_inv p w cc ax))"

definition valid_ua :: "args \<Rightarrow> eaggp \<Rightarrow> ts \<Rightarrow> uwagg \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_ua args p cur a auxlist \<longleftrightarrow>
     (\<exists>u. ua_rel p (args_n args) a u \<and> valid_uw args cur u auxlist) \<and>
     length (args_R args) = args_n args \<and> eagg_ok p (args_n args)"

section \<open>The executable fused Until window\<close>

text \<open>
  The theory above fuses the aggregation into the Until window.  The
  executable window is the same structure with the count structure kept without its key set, as
  the executable fused Since window of @{theory MFODL_Monitor_Exec.Since_Agg} keeps it: it reports
  the aggregate rather than the union, so the mapping answers everything it asks.  There is no
  invariant here -- that stayed a level below, in @{const valid_ua}.
\<close>

type_synonym uuwauxm = "ts queue \<times> uw_entry queue \<times> uw_entry queue \<times> nat \<times> bool \<times>
  ucnt \<times> event_data list set list"

type_synonym uuwagg = "uuwauxm \<times> ugagg option"

definition uuwm_init :: "args \<Rightarrow> uuwauxm" where
  "uuwm_init args = (empty_queue, empty_queue, empty_queue, 0, True, Mapping.empty, [])"

fun uuwm :: "uuwauxm \<Rightarrow> uwaux" where
  "uuwm (nts, win, rest, len, bend, cc, dn) = (nts, win, rest, len, bend, ucc cc, dn)"

declare uuwm.simps[simp del]

lemma uuwm_init_ucc: "uw_init args = uuwm (uuwm_init args)"
  by (simp add: uw_init_def uuwm_init_def uuwm.simps ucc.simps)

function uua_extend :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uw_entry queue \<Rightarrow> uw_entry queue \<Rightarrow> bool \<Rightarrow>
    ucnt \<Rightarrow> ugagg option \<Rightarrow>
    uw_entry queue \<times> uw_entry queue \<times> bool \<times> ucnt \<times> ugagg option" where
  "uua_extend args p w ts0 win rest bend cc ax =
     (if \<not> bend then (win, rest, bend, cc, ax)
      else (case safe_hd rest of
              (None, rest') \<Rightarrow> (win, rest', bend, cc, ax)
            | (Some e, rest') \<Rightarrow>
                (if memR (args_ivl args) (fst e - ts0)
                 then uua_extend args p w ts0 (append_queue e win) (tl_queue rest')
                        (snd (snd e)) (ucnt_add (fst (snd e)) cc)
                        (uag_ins p w (fst (snd e)) cc ax)
                 else (win, rest', bend, cc, ax))))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, w, ts0, win, rest, bend, cc, ax). length (linearize rest))")
     (fastforce split: prod.splits)+

declare uua_extend.simps[simp del]

definition uua_init :: "args \<Rightarrow> eaggp \<Rightarrow> uuwagg" where
  "uua_init args p = (uuwm_init args, ag_init p (args_n args))"

definition uua_step :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uuwagg \<Rightarrow> uuwagg" where
  "uua_step args p w ts0 a = (case a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
     (case uua_extend args p w ts0 win rest bend cc ax of (win, rest, bend, cc, ax) \<Rightarrow>
        (case safe_hd win of
           (None, win') \<Rightarrow> ((tl_queue nts, win', rest, len - 1, bend, cc,
                             uag_res None p w cc ax # dn), ax)
         | (Some e, win') \<Rightarrow>
           (let win'' = tl_queue win';
                r = uag_res None p w cc ax;
                cc' = ucnt_del (fst (snd e)) cc;
                ax' = uag_del p w (fst (snd e)) cc ax;
                bend' = (if Queue.is_empty win'' then True else bend)
            in ((tl_queue nts, win'', rest, len - 1, bend', cc', r # dn), ax')))))"

function uua_shift :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uuwagg \<Rightarrow> uuwagg" where
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

definition uua_add_new :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> event_data list set \<Rightarrow> ts \<Rightarrow>
    uuwagg \<Rightarrow> uuwagg" where
  "uua_add_new args p w rel1 rel2 nt a =
     (case uua_shift args p w nt a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in ((append_queue nt nts, win, append_queue (nt, rel2, b) rest, len + 1, bend, cc, dn), ax)))"

definition uua_eval :: "args \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> uuwagg \<Rightarrow>
    event_data list set list \<times> uuwagg" where
  "uua_eval args p w nt a =
     (case uua_shift args p w nt a of ((nts, win, rest, len, bend, cc, dn), ax) \<Rightarrow>
       (rev dn, ((nts, win, rest, len, bend, cc, []), ax)))"

subsection \<open>The refinement of the executable window\<close>

fun rua :: "uuwagg \<Rightarrow> uwagg" where
  "rua (w, ax) = (uuwm w, ax)"

declare rua.simps[simp del]

lemma fst_rua[simp]: "fst (rua a) = uuwm (fst a)"
  by (cases a) (simp add: rua.simps)

lemma snd_rua[simp]: "snd (rua a) = snd a"
  by (cases a) (simp add: rua.simps)

lemma rua_init: "rua (uua_init args p) = ua_init args p"
  by (simp add: rua.simps uua_init_def ua_init_def uuwm_init_ucc)

(*<*)
end
(*>*)
