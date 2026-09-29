(*<*)
theory Dense_Maux
  imports Dense_Win "MFODL_Monitor_Devel.Monitor_Impl"
begin
(*>*)

text \<open>As in @{theory MFODL_Monitor_Devel.Monitor_Impl}, whose simpset the merge with
  @{theory MFODL_Monitor_Dense.Dense_Win}'s imports would otherwise extend.\<close>

declare Let_def[simp del]

section \<open>The window structures the monitor runs\<close>

text \<open>
  The kernel is generic in its window structures (locale @{locale maux}).  The monitor runs it
  with the kernel's own structures, except that a Since whose left operand is closed and which
  carries no aggregation uses the sliding window of @{theory MFODL_Monitor_Dense.Dense_Win}: the
  choice is made once, when the structure is initialised, from the operator's arguments.
\<close>

subsection \<open>Since\<close>

datatype dsaux = DS_gen mmasaux | DS_win swaux

definition ds_win_args :: "args \<Rightarrow> bool" where
  "ds_win_args args \<longleftrightarrow> args_L args = [] \<and> args_agg args = None"

fun valid_dsaux :: "args \<Rightarrow> ts \<Rightarrow> dsaux \<Rightarrow> event_data msaux \<Rightarrow> bool" where
  "valid_dsaux args cur (DS_gen aux) auxlist = valid_mmasaux args cur aux auxlist"
| "valid_dsaux args cur (DS_win aux) auxlist = (ds_win_args args \<and> valid_sw args cur aux auxlist)"

definition init_dsaux :: "args \<Rightarrow> dsaux" where
  "init_dsaux args = (if ds_win_args args then DS_win (sw_init args) else DS_gen (init_mmasaux args))"

fun add_new_ts_dsaux :: "args \<Rightarrow> ts \<Rightarrow> dsaux \<Rightarrow> dsaux" where
  "add_new_ts_dsaux args nt (DS_gen aux) = DS_gen (add_new_ts_mmasaux args nt aux)"
| "add_new_ts_dsaux args nt (DS_win aux) = DS_win (sw_add_new_ts args nt aux)"

fun join_dsaux :: "args \<Rightarrow> event_data table \<Rightarrow> dsaux \<Rightarrow> dsaux" where
  "join_dsaux args X (DS_gen aux) = DS_gen (gc_join_mmasaux args X aux)"
| "join_dsaux args X (DS_win aux) = DS_win (sw_join args X aux)"

fun add_new_table_dsaux :: "args \<Rightarrow> event_data table \<Rightarrow> dsaux \<Rightarrow> dsaux" where
  "add_new_table_dsaux args X (DS_gen aux) = DS_gen (add_new_table_mmasaux args X aux)"
| "add_new_table_dsaux args X (DS_win aux) = DS_win (sw_add_new_table args X aux)"

fun result_dsaux :: "args \<Rightarrow> dsaux \<Rightarrow> event_data table" where
  "result_dsaux args (DS_gen aux) = result_mmasaux args aux"
| "result_dsaux args (DS_win aux) = sw_result args aux"

lemma valid_init_dsaux:
  "set L \<subseteq> set R \<Longrightarrow> distinct L \<Longrightarrow> distinct R \<Longrightarrow> valid_aggargs n R agg \<Longrightarrow>
    valid_dsaux (init_args I n L R pos agg) 0 (init_dsaux (init_args I n L R pos agg)) []"
  by (cases "ds_win_args (init_args I n L R pos agg)")
    (simp_all only: init_dsaux_def if_True if_False valid_dsaux.simps valid_sw_init
      default_mmasaux.valid_init_msaux simp_thms)

lemma valid_add_new_ts_dsaux: "valid_dsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    valid_dsaux args nt (add_new_ts_dsaux args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  by (cases aux) (simp_all only: valid_dsaux.simps add_new_ts_dsaux.simps
    default_mmasaux.valid_add_new_ts_msaux simp_thms, blast intro: valid_sw_add_new_ts)

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
qed (simp only: valid_dsaux.simps join_dsaux.simps default_mmasaux.valid_join_msaux)

lemma valid_add_new_table_dsaux: "valid_dsaux args cur aux auxlist \<Longrightarrow> table (args_R args) rel2 \<Longrightarrow>
    valid_dsaux args cur (add_new_table_dsaux args rel2 aux)
    (case auxlist of
      [] => [(cur, rel2)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
  by (cases aux) (simp_all only: valid_dsaux.simps add_new_table_dsaux.simps
    default_mmasaux.valid_add_new_table_msaux valid_sw_add_new_table simp_thms)

lemma valid_result_dsaux: "valid_dsaux args cur aux auxlist \<Longrightarrow> result_dsaux args aux =
    eval_args_agg args (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof (cases aux)
  case (DS_win w)
  assume "valid_dsaux args cur aux auxlist"
  with DS_win have "args_agg args = None" "valid_sw args cur w auxlist"
    by (simp_all add: ds_win_args_def)
  with DS_win show ?thesis
    by (simp only: result_dsaux.simps valid_sw_result eval_args_agg_def option.case)
qed (simp only: valid_dsaux.simps result_dsaux.simps default_mmasaux.valid_result_msaux)

interpretation dense_msaux: msaux valid_dsaux init_dsaux add_new_ts_dsaux join_dsaux
  add_new_table_dsaux result_dsaux
  by unfold_locales (fact valid_init_dsaux valid_add_new_ts_dsaux valid_join_dsaux
    valid_add_new_table_dsaux valid_result_dsaux)+

subsection \<open>The monitor's instance of the kernel\<close>

global_interpretation dense_maux: maux
  (* msaux *) valid_dsaux init_dsaux add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux
  (* muaux *) valid_muaux_dq "init_muaux_dq :: _ \<Rightarrow> muaux_dq" add_new_muaux_dq
    length_muaux_dq eval_muaux_dq
  (* mtaux *) valid_mmtaux init_mmtaux update_mmtaux result_mmtaux
  defines dminit0 = "maux.minit0 init_dsaux (init_muaux_dq :: _ \<Rightarrow> muaux_dq) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and dminit = "maux.minit init_dsaux (init_muaux_dq :: _ \<Rightarrow> muaux_dq) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and dminit_safe = "maux.minit_safe init_dsaux (init_muaux_dq :: _ \<Rightarrow> muaux_dq) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and dmeval_since = "maux.eval_since add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux"
  and dmeval = "maux.meval add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and dletpast_meval = "maux.letpast_meval add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and dmstep = "maux.mstep add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and dmsteps0_stateless = "maux.msteps0_stateless add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and dmsteps_stateless = "maux.msteps_stateless add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and dmonitor = "maux.monitor init_dsaux add_new_ts_dsaux join_dsaux add_new_table_dsaux result_dsaux init_muaux_dq add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) init_mmtaux update_mmtaux result_mmtaux"
  by unfold_locales

type_synonym dmstate = "(dsaux, muaux_dq, event_data mmtaux) mstate"

text \<open>The initial state is computed by @{const dminit0} itself; the locales' initialisers of the
  temporal nodes are unfolded into its code, as for the kernel's default instance.\<close>

declare dense_msaux.init_since_def[code_unfold] dq_muaux.init_until_def[code_unfold]
  verimon_maux.init_trigger_def[code_unfold]

lemmas dminit0_code_simps = dense_maux.minit0.simps[unfolded verimon_maux.init_and_trigger_def]

declare [[code drop: dminit0]]
declare dminit0_code_simps[code]

(*<*)
end
(*>*)
