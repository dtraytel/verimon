(*<*)
theory Dense_Imp_Code_Opt
  imports Dense_Imp "MFODL_Monitor_Dense.Dense_Mono_Sweep"
begin
(*>*)

section \<open>The heap-resident structures of the dense monitor, specialised\<close>

text \<open>
  @{theory MFODL_Monitor_Dense.Dense_Code_Opt} and @{theory MFODL_Monitor_Dense.Dense_Mono_Sweep}
  specialise the pure containers the verified dense evaluator uses, and the shipping export
  (theory Monitor\_Code\_Dense of session MFODL\_Monitor\_Dense) is built with them.  The heap-resident
  monitor of @{theory MFODL_Monitor_Imp.Dense_Imp} uses two structures of its own on top of
  those, and they get the same treatment here.
\<close>

subsection \<open>The heap index of the dense join\<close>

text \<open>
  The operations of @{theory MFODL_Monitor_Imp.Table_Imp} take the @{class heap} dictionary of
  the key type and of the value type, and the code generator builds both at every call.  The
  index of the join over the wide tuples is boxed for that reason in
  @{theory MFODL_Monitor_Imp.Join_Imp2}; the one over the short tuples is entered once per
  indexed and once per probed tuple, so it needs the same.
\<close>

setup \<open>Monomorphize.box_cmd
  (let val edl = "event_data list"; val edll = "event_data list list" in
    [("im_lookup_h", "djidx_lookup_h_v", [edl, edll]),
     ("im_update_h", "djidx_update_h_v", [edl, edll]),
     ("im_new", "djidx_new_v", [edl, edll])] end)\<close>

subsection \<open>The heap-resident Since\<close>

text \<open>
  The heap-resident Since is generic in its tuple type rather than its element type, and is used
  at both, so it is specialised twice.
\<close>

ML \<open>
val heap_since_consts =
  ["gjc", "filter_loop2", "expire_loop2", "upd_loop2", "move_loop2",
   "del_loop2", "ins_loop2", "since_loop2", "init2", "shift_end2",
   "add_new_ts2'", "add_new_ts2", "gc2", "join2", "gc_join2",
   "add_new_table2", "result2"]
\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (map (fn c => (c, mono_name "hsd_" c, ["event_data list"])) heap_since_consts
   @ map (fn c => (c, mono_name "hsw_" c, ["event_data tuple"])) heap_since_consts)
  ["edl_dict_simps", "etuple_dict_simps"]\<close>

(*<*)
end
(*>*)
