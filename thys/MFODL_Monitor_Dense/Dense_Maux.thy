(*<*)
theory Dense_Maux
  imports Dense_Win_Agg "MFODL_Monitor_Devel.Monitor_Impl"
begin
(*>*)

text \<open>As in @{theory MFODL_Monitor_Devel.Monitor_Impl}, whose simpset the merge with
  @{theory MFODL_Monitor_Dense.Dense_Win}'s imports would otherwise extend.\<close>

declare Let_def[simp del]

section \<open>The window structures the monitor runs\<close>

text \<open>
  The kernel is generic in its window structures (locale @{locale maux}).  The monitor runs it
  with the kernel's own structures, except that a Since or an Until whose left operand is closed
  uses the sliding windows of @{theory MFODL_Monitor_Dense.Dense_Win} (for a Since with an
  aggregation, the window of @{theory MFODL_Monitor_Dense.Dense_Win_Agg}): the choice is made once,
  when the structure is initialised, from the operator's arguments.
\<close>

subsection \<open>Since\<close>

datatype dsaux = DS_gen mmasaux | DS_win swaux | DS_agg aggargs swaaux

definition ds_win_args :: "args \<Rightarrow> bool" where
  "ds_win_args args \<longleftrightarrow> args_L args = [] \<and> args_agg args = None"

fun valid_dsaux :: "args \<Rightarrow> ts \<Rightarrow> dsaux \<Rightarrow> event_data msaux \<Rightarrow> bool" where
  "valid_dsaux args cur (DS_gen aux) auxlist = valid_mmasaux args cur aux auxlist"
| "valid_dsaux args cur (DS_win aux) auxlist = (ds_win_args args \<and> valid_sw args cur aux auxlist)"
| "valid_dsaux args cur (DS_agg ag aux) auxlist =
    (args_L args = [] \<and> args_agg args = Some ag \<and> valid_swa ag args cur aux auxlist)"

definition init_dsaux :: "args \<Rightarrow> dsaux" where
  "init_dsaux args = (if args_L args = []
     then (case args_agg args of None \<Rightarrow> DS_win (sw_init args) | Some ag \<Rightarrow> DS_agg ag (swa_init ag args))
     else DS_gen (init_mmasaux args))"

fun add_new_ts_dsaux :: "args \<Rightarrow> ts \<Rightarrow> dsaux \<Rightarrow> dsaux" where
  "add_new_ts_dsaux args nt (DS_gen aux) = DS_gen (add_new_ts_mmasaux args nt aux)"
| "add_new_ts_dsaux args nt (DS_win aux) = DS_win (sw_add_new_ts args nt aux)"
| "add_new_ts_dsaux args nt (DS_agg ag aux) = DS_agg ag (swa_add_new_ts ag args nt aux)"

fun join_dsaux :: "args \<Rightarrow> event_data table \<Rightarrow> dsaux \<Rightarrow> dsaux" where
  "join_dsaux args X (DS_gen aux) = DS_gen (gc_join_mmasaux args X aux)"
| "join_dsaux args X (DS_win aux) = DS_win (sw_join args X aux)"
| "join_dsaux args X (DS_agg ag aux) = DS_agg ag (swa_join ag args X aux)"

fun add_new_table_dsaux :: "args \<Rightarrow> event_data table \<Rightarrow> dsaux \<Rightarrow> dsaux" where
  "add_new_table_dsaux args X (DS_gen aux) = DS_gen (add_new_table_mmasaux args X aux)"
| "add_new_table_dsaux args X (DS_win aux) = DS_win (sw_add_new_table args X aux)"
| "add_new_table_dsaux args X (DS_agg ag aux) = DS_agg ag (swa_add_new_table ag args X aux)"

fun result_dsaux :: "args \<Rightarrow> dsaux \<Rightarrow> event_data table" where
  "result_dsaux args (DS_gen aux) = result_mmasaux args aux"
| "result_dsaux args (DS_win aux) = sw_result args aux"
| "result_dsaux args (DS_agg ag aux) = swa_result ag args aux"

lemma valid_init_dsaux:
  assumes "set L \<subseteq> set R" "distinct L" "distinct R" "valid_aggargs n R agg"
  shows "valid_dsaux (init_args I n L R pos agg) 0 (init_dsaux (init_args I n L R pos agg)) []"
proof (cases "args_L (init_args I n L R pos agg) = []")
  case True
  then show ?thesis
    by (cases agg) (simp_all add: init_dsaux_def ds_win_args_def valid_sw_init valid_swa_init
      init_args_def)
next
  case False
  then show ?thesis using default_mmasaux.valid_init_msaux[OF assms]
    by (simp only: init_dsaux_def if_False valid_dsaux.simps)
qed

lemma valid_add_new_ts_dsaux: "valid_dsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    valid_dsaux args nt (add_new_ts_dsaux args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  by (cases aux) (simp_all only: valid_dsaux.simps add_new_ts_dsaux.simps
    default_mmasaux.valid_add_new_ts_msaux simp_thms,
    blast intro: valid_sw_add_new_ts, blast intro: valid_swa_add_new_ts)

lemma valid_join_dsaux: "valid_dsaux args cur aux auxlist \<Longrightarrow> table (args_L args) rel1 \<Longrightarrow>
    valid_dsaux args cur (join_dsaux args rel1 aux)
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist)"
proof (cases aux)
  case (DS_win w)
  assume "valid_dsaux args cur aux auxlist" "table (args_L args) rel1"
  with DS_win have "ds_win_args args" "valid_sw args cur w auxlist" "table [] rel1"
    "args_L args = []"
    by (simp_all add: ds_win_args_def)
  with DS_win show ?thesis
    by (simp only: valid_dsaux.simps join_dsaux.simps simp_thms) (auto intro: valid_sw_join)
next
  case (DS_agg ag w)
  assume "valid_dsaux args cur aux auxlist" "table (args_L args) rel1"
  with DS_agg have "args_agg args = Some ag" "valid_swa ag args cur w auxlist" "table [] rel1"
    "args_L args = []"
    by simp_all
  with DS_agg show ?thesis
    by (simp only: valid_dsaux.simps join_dsaux.simps simp_thms) (auto intro: valid_swa_join)
qed (simp only: valid_dsaux.simps join_dsaux.simps default_mmasaux.valid_join_msaux)

lemma valid_add_new_table_dsaux: "valid_dsaux args cur aux auxlist \<Longrightarrow> table (args_R args) rel2 \<Longrightarrow>
    valid_dsaux args cur (add_new_table_dsaux args rel2 aux)
    (case auxlist of
      [] => [(cur, rel2)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
  by (cases aux) (simp_all only: valid_dsaux.simps add_new_table_dsaux.simps
    default_mmasaux.valid_add_new_table_msaux valid_sw_add_new_table valid_swa_add_new_table
    simp_thms)

lemma valid_result_dsaux: "valid_dsaux args cur aux auxlist \<Longrightarrow> result_dsaux args aux =
    eval_args_agg args (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof (cases aux)
  case (DS_win w)
  assume "valid_dsaux args cur aux auxlist"
  with DS_win have "args_agg args = None" "valid_sw args cur w auxlist"
    by (simp_all add: ds_win_args_def)
  with DS_win show ?thesis
    by (simp only: result_dsaux.simps valid_sw_result eval_args_agg_def option.case)
next
  case (DS_agg ag w)
  assume "valid_dsaux args cur aux auxlist"
  with DS_agg have "args_agg args = Some ag" "valid_swa ag args cur w auxlist"
    by simp_all
  with DS_agg show ?thesis
    by (simp only: result_dsaux.simps valid_swa_result eval_args_agg_def option.case)
qed (simp only: valid_dsaux.simps result_dsaux.simps default_mmasaux.valid_result_msaux)

interpretation dense_msaux: msaux valid_dsaux init_dsaux add_new_ts_dsaux join_dsaux
  add_new_table_dsaux result_dsaux
  by unfold_locales (fact valid_init_dsaux valid_add_new_ts_dsaux valid_join_dsaux
    valid_add_new_table_dsaux valid_result_dsaux)+

subsection \<open>Until\<close>

text \<open>An Until whose left operand is closed, which carries no aggregation, and whose interval
  contains 0 uses the window of @{theory MFODL_Monitor_Dense.Dense_Win}.\<close>

datatype duaux = DU_gen muaux_dq | DU_win uwaux

definition du_win_args :: "args \<Rightarrow> bool" where
  "du_win_args args \<longleftrightarrow> args_L args = [] \<and> args_agg args = None \<and> memL (args_ivl args) 0"

fun valid_duaux :: "args \<Rightarrow> ts \<Rightarrow> duaux \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_duaux args cur (DU_gen aux) auxlist = valid_muaux_dq args cur aux auxlist"
| "valid_duaux args cur (DU_win aux) auxlist = (du_win_args args \<and> valid_uw args cur aux auxlist)"

definition init_duaux :: "args \<Rightarrow> duaux" where
  "init_duaux args = (if du_win_args args then DU_win (uw_init args) else DU_gen (init_muaux_dq args))"

fun add_new_duaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> duaux \<Rightarrow> duaux" where
  "add_new_duaux args rel1 rel2 nt (DU_gen aux) = DU_gen (add_new_muaux_dq args rel1 rel2 nt aux)"
| "add_new_duaux args rel1 rel2 nt (DU_win aux) = DU_win (uw_add_new args rel1 rel2 nt aux)"

fun length_duaux :: "args \<Rightarrow> duaux \<Rightarrow> nat" where
  "length_duaux args (DU_gen aux) = length_muaux_dq args aux"
| "length_duaux args (DU_win aux) = uw_length args aux"

fun eval_duaux :: "args \<Rightarrow> ts \<Rightarrow> duaux \<Rightarrow> event_data table list \<times> duaux" where
  "eval_duaux args nt (DU_gen aux) = map_prod id DU_gen (eval_muaux_dq args nt aux)"
| "eval_duaux args nt (DU_win aux) = map_prod id DU_win (uw_eval args nt aux)"

lemma valid_init_duaux:
  "set L \<subseteq> set R \<Longrightarrow> distinct L \<Longrightarrow> distinct R \<Longrightarrow> valid_aggargs n R agg \<Longrightarrow>
    valid_duaux (init_args I n L R pos agg) 0 (init_duaux (init_args I n L R pos agg)) []"
  by (cases "du_win_args (init_args I n L R pos agg)")
    (simp_all only: init_duaux_def if_True if_False valid_duaux.simps valid_uw_init
      dq_muaux.valid_init_muaux simp_thms)

lemma valid_add_new_duaux: "valid_duaux args cur aux auxlist \<Longrightarrow> table (args_L args) rel1 \<Longrightarrow>
    table (args_R args) rel2 \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    valid_duaux args nt (add_new_duaux args rel1 rel2 nt aux) (update_until args rel1 rel2 nt auxlist)"
proof (cases aux)
  case (DU_win w)
  assume "valid_duaux args cur aux auxlist" "table (args_L args) rel1" "table (args_R args) rel2"
    "nt \<ge> cur"
  with DU_win have "du_win_args args" "valid_uw args cur w auxlist" "table [] rel1"
    "args_L args = []" "memL (args_ivl args) 0" "table (args_R args) rel2" "cur \<le> nt"
    by (simp_all add: du_win_args_def)
  with DU_win show ?thesis
    by (simp only: valid_duaux.simps add_new_duaux.simps simp_thms)
      (auto intro: valid_uw_add_new)
qed (simp only: valid_duaux.simps add_new_duaux.simps dq_muaux.valid_add_new_muaux)

lemma valid_length_duaux: "valid_duaux args cur aux auxlist \<Longrightarrow> length_duaux args aux = length auxlist"
  by (cases aux) (simp_all only: valid_duaux.simps length_duaux.simps
    dq_muaux.valid_length_muaux, blast dest: valid_uw_length)

lemma valid_eval_duaux: "valid_duaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    eval_duaux args nt aux = (res, aux') \<Longrightarrow> eval_until (args_ivl args) nt auxlist = (res', auxlist') \<Longrightarrow>
    valid_duaux args cur aux' auxlist' \<and> res = map (eval_args_agg args) res'"
proof (cases aux)
  case (DU_gen w)
  assume v: "valid_duaux args cur aux auxlist" and cn: "nt \<ge> cur"
    and ev: "eval_duaux args nt aux = (res, aux')"
    and eu: "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  obtain r w' where e: "eval_muaux_dq args nt w = (r, w')" by fastforce
  with ev DU_gen have "res = r" "aux' = DU_gen w'" by simp_all
  with dq_muaux.valid_eval_muaux[OF _ cn e eu] v DU_gen show ?thesis by simp
next
  case (DU_win w)
  assume v: "valid_duaux args cur aux auxlist" and cn: "nt \<ge> cur"
    and ev: "eval_duaux args nt aux = (res, aux')"
    and eu: "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  obtain r w' where e: "uw_eval args nt w = (r, w')" by (cases "uw_eval args nt w")
  with ev DU_win have "res = r" "aux' = DU_win w'" by simp_all
  moreover have "du_win_args args" "valid_uw args cur w auxlist" using v DU_win by simp_all
  moreover have "eval_args_agg args = id"
    using \<open>du_win_args args\<close> by (auto simp: du_win_args_def eval_args_agg_def)
  ultimately show ?thesis using valid_uw_eval[OF _ cn e eu] by simp
qed

interpretation dense_muaux: muaux valid_duaux init_duaux add_new_duaux length_duaux eval_duaux
  by unfold_locales (fact valid_init_duaux valid_add_new_duaux valid_length_duaux valid_eval_duaux)+

subsection \<open>The monitor's instance of the kernel\<close>

global_interpretation dense_maux: maux
  (* msaux *) valid_dsaux init_dsaux add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux
  (* muaux *) valid_duaux init_duaux add_new_duaux length_duaux eval_duaux
  (* mtaux *) valid_mmtaux init_mmtaux update_mmtaux result_mmtaux
  defines dminit0 = "maux.minit0 init_dsaux init_duaux (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and dminit = "maux.minit init_dsaux init_duaux (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and dminit_safe = "maux.minit_safe init_dsaux init_duaux (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and dmeval_since = "maux.eval_since add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux"
  and dmeval = "maux.meval add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_duaux eval_duaux update_mmtaux result_mmtaux"
  and dletpast_meval = "maux.letpast_meval add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_duaux eval_duaux update_mmtaux result_mmtaux"
  and dmstep = "maux.mstep add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_duaux eval_duaux update_mmtaux result_mmtaux"
  and dmsteps0_stateless = "maux.msteps0_stateless add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_duaux eval_duaux update_mmtaux result_mmtaux"
  and dmsteps_stateless = "maux.msteps_stateless add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_duaux eval_duaux update_mmtaux result_mmtaux"
  and dmonitor = "maux.monitor init_dsaux add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux init_duaux add_new_duaux eval_duaux init_mmtaux update_mmtaux result_mmtaux"
  by unfold_locales

type_synonym dmstate = "(dsaux, duaux, event_data mmtaux) mstate"

text \<open>The initial state is computed by @{const dminit0} itself; the locales' initialisers of the
  temporal nodes are unfolded into its code, as for the kernel's default instance.\<close>

declare dense_msaux.init_since_def[code_unfold] dense_muaux.init_until_def[code_unfold]
  verimon_maux.init_trigger_def[code_unfold]

lemmas dminit0_code_simps = dense_maux.minit0.simps[unfolded verimon_maux.init_and_trigger_def]

declare [[code drop: dminit0]]
declare dminit0_code_simps[code]

(*<*)
end
(*>*)
