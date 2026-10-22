(*<*)
theory Mono_Hot_Proof
  imports "Monitor_Exec.Mono_Hot" RBT_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>
  @{theory MFODL_Monitor_Exec.Mono_Sweep} ends with the claim that what is left generic
  is cold.  A profile of the export says otherwise for a handful of operations, all of them at
  the tuples, and all for one of three reasons.

  \<^item> \<^emph>\<open>A copy is missing.\<close>  Without copies of their own at @{typ "event_data list"},
    the sorted list of a table and the filter of a count map pass the dictionary down, so the
    tree operations inside reach the composite comparator
    @{text "comparator_list comparator_event_data"} through a closure.
  \<^item> \<^emph>\<open>A fold is generic while its step is not.\<close>  @{theory MFODL_Monitor_Exec.Map_Upd_Code}
    specialises the grouped aggregation's steps @{const gstep_ins} and @{const gstep_del} at
    @{typ event_data}, but not the folds @{const gins} and @{const gdel} over them, nor the
    result @{const gres}, @{const gmr} and the initial state @{const ginit}; the window
    aggregate over a group calls all of these at @{typ event_data}, so it runs the generic
    steps, and their generic one-descent updates and lookups, after all.  On the aggregation
    benchmark that is about a tenth of the run inclusive.
  \<^item> \<^emph>\<open>A dictionary is built per call.\<close>  The one-descent updates of
    @{theory MFODL_Monitor_Exec.Map_Upd_Code} return a pair containing a tree, and
    @{command lift_definition}'s option @{text code_dt} puts the pair behind an isomorphism whose projection
    takes the key type's @{class ccompare} dictionary without using it.  The monomorphic
    updates call that projection with the dictionary built on the spot, once per update.
\<close>

text \<open>The intersection of two tables is the tree intersection of
  @{theory Deriving.RBT_Comparator_Impl} with @{const ed_comparator} passed as its argument, so
  its lookups (the small operand's keys looked up in the other tree) and its splits call the
  comparator through a closure.  These are its copies at that comparator, as
  @{theory MFODL_Monitor_Exec.Map_Upd_Code} has them for the union and the difference.\<close>

end
(*>*)
