(*<*)
theory Table_Evt
  imports "MFODL_Monitor_Devel.Monomorphic_Code"
begin
(*>*)

section \<open>The union of a window of tables, as a count per tuple\<close>

text \<open>Adding a table to the union costs one update per tuple of that table, removing one costs
the same, and the union itself changes only where a count reaches or leaves zero.  Both the
Since and the Until structure for a closed left operand are built on this.\<close>

definition evt_add :: "event_data table \<Rightarrow> (event_data tuple, nat) mapping \<times> event_data table \<Rightarrow>
    (event_data tuple, nat) mapping \<times> event_data table" where
  "evt_add T cc = fold (\<lambda>t (c, s). case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, Set.insert t s)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, s)) (csorted_list_of_set T) cc"

definition evt_del :: "event_data table \<Rightarrow> (event_data tuple, nat) mapping \<times> event_data table \<Rightarrow>
    (event_data tuple, nat) mapping \<times> event_data table" where
  "evt_del T cc = fold (\<lambda>t (c, s). case Mapping.lookup c t of
       None \<Rightarrow> (c, s)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, Set.remove t s)
                  else (Mapping.update t (k - 1) c, s))) (csorted_list_of_set T) cc"

(*<*)
end
(*>*)