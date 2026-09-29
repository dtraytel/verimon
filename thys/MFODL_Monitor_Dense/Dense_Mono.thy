(*<*)
theory Dense_Mono
  imports Kernel_Code
begin
(*>*)

section \<open>The generic operations left on the monitor's inner loops\<close>

text \<open>
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} gives the kernel's operations at the tuples of
  @{typ event_data} monomorphic copies, in which the comparator of the tuples is
  @{const ed_comparator} rather than the generic comparator on lists, reached through a closure
  for every element compared.  A profile of the export finds three kinds of generic code left on
  the inner loops.
  \<^item> The copy @{text ed_join} of the plain join was derived from the join's code equations of
    the time; @{theory MFODL_Monitor_Dense.Kernel_Code} has since replaced those.
  \<^item> The derivatives of the regular expressions, and the Since structure's index operations,
    have no copies, so the join and the tree operations they call run generically.
  \<^item> The grouping of a table by a key (@{const cluster}) is boxed rather than copied: the box
    builds the dictionary once and passes it, so the comparator is still the generic one.
\<close>

subsection \<open>The plain join\<close>

declare [[code drop: ed_join]]

lemmas ed_join_code[code] = join_key_code[where 'a = event_data, folded ed_join_def]

subsection \<open>The copies\<close>

text \<open>The box of @{const cluster} would shadow its copy.\<close>

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt delsimps @{thms ed_cluster_v_unfold})\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("cluster", "ed_cluster", [etuple, etuple]),
   ("reorder", "ed_reorder", ["event_data"]),
   ("\<epsilon>_lax", "ed_eps_lax", ["event_data"]),
   ("r\<epsilon>_strict", "ed_reps_strict", ["event_data"]),
   ("l\<epsilon>_strict", "ed_leps_strict", ["event_data"]),
   ("r\<delta>", "ed_rdelta", ["event_data"]),
   ("l\<delta>", "ed_ldelta", ["event_data"]),
   ("wf_set_of_set", "ed_wf_set_of_set", ["event_data"]),
   ("wf_table_set", "ed_wf_table_set", ["event_data"]),
   ("wf_table_union", "ed_wf_table_union", ["event_data"]),
   ("wf_table_join", "ed_wf_table_join", ["event_data"]),
   ("wf_table_antijoin", "ed_wf_table_antijoin", ["event_data"]),
   ("wf_idx_of_set", "ed_wf_idx_of_set", ["event_data"]),
   ("wf_idx_union", "ed_wf_idx_union", ["event_data"]),
   ("wf_idx_antijoin", "ed_wf_idx_antijoin", ["event_data"]),
   ("move_insert", "ed_move_insert", ["event_data"]),
   ("move_tbl", "ed_move_tbl", ["event_data"]),
   ("tmp_elem", "ed_tmp_elem", ["event_data"]),
   ("until_step", "ed_until_step", ["event_data"])]
  ["etuple_dict_simps"]\<close>

text \<open>The copies made in @{theory MFODL_Monitor_Devel.Monomorphic_Code} were derived through the
  box, and call it: the box is the copy.\<close>

declare [[code drop: ed_cluster_v]]

lemma ed_cluster_v_code[code]: "ed_cluster_v = Box ed_cluster"
  by (simp add: ed_cluster_v_def ed_cluster_def)

text \<open>The Since structure's index is built through @{const wf_table_of_set_args}, which has no
  copy either; nor has the tree's key list, which the count sets of
  \<^verbatim>\<open>Dense_Win\<close> fold over.  And the boxes of the Since structure's
  mapping operations pass the generic comparator down: they become copies too.\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("wf_table_of_set_args", "ed_wf_table_of_set_args", ["event_data"]),
   ("wf_idx_of_wf_set", "ed_wf_idx_of_wf_set", ["event_data"]),
   ("wf_set_union", "ed_wf_set_union", ["event_data"]),
   ("RBT_Set2.keys", "ed_rbt_keys", [etuple]),
   ("upd_set", "ed_upd_set_nat_m", [etuple, "nat"]),
   ("minus_keys", "ed_minus_keys_m", [etuple, "nat"]),
   ("mapping_delete_set", "ed_mapping_delete_set_tstp_m", [etuple, "nat + nat"]),
   ("filter_set", "ed_filter_set_m", ["nat", etuple]),
   ("set_of_idx", "ed_set_of_idx_m", [etuple, etuple]),
   ("mapping_of_cluster", "ed_mapping_of_cluster", [etuple, etuple]),
   ("cluster_rbt_comp", "ed_cluster_rbt_comp", [etuple, etuple]),
   ("add_to_rbt_comp", "ed_add_to_rbt_comp", [etuple, etuple])]
  ["etuple_dict_simps"]\<close>

declare [[code drop: ed_upd_set_nat_v ed_minus_keys_v ed_mapping_delete_set_tstp_v ed_filter_set_v
  ed_set_of_idx_v]]

lemma ed_box_copies[code]:
  "ed_upd_set_nat_v = Box ed_upd_set_nat_m"
  "ed_minus_keys_v = Box ed_minus_keys_m"
  "ed_mapping_delete_set_tstp_v = Box ed_mapping_delete_set_tstp_m"
  "ed_filter_set_v = Box ed_filter_set_m"
  "ed_set_of_idx_v = Box ed_set_of_idx_m"
  by (simp_all add: ed_upd_set_nat_v_def ed_upd_set_nat_m_def ed_minus_keys_v_def ed_minus_keys_m_def
    ed_mapping_delete_set_tstp_v_def ed_mapping_delete_set_tstp_m_def ed_filter_set_v_def
    ed_filter_set_m_def ed_set_of_idx_v_def ed_set_of_idx_m_def)

(*<*)
end
(*>*)
