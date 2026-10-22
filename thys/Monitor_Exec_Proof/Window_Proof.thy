(*<*)
theory Window_Proof
  imports "Monitor_Exec.Window" Tuple_Fields_Proof "Monitor_Impl_Proof.Optimized_Until_Deque_Proof" "Monitor_Impl_Proof.Optimized_Trigger_Proof" "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



subsection \<open>Two facts about the closed left operand\<close>

text \<open>Joining a table with a table over no columns keeps it or empties it, depending only on
  whether that table is empty and on the polarity.\<close>

text \<open>A predicate on timestamps that only fails further to the right cuts a sorted list into a
  prefix and a suffix, so the two scans coincide with the two filters.\<close>

subsubsection \<open>What the two scans do to the queues\<close>

text \<open>Appending an entry to a run extends every answer by the new table exactly when the new
  timestamp is in range from the run's start and the left operand held throughout the run.\<close>

text \<open>After the extension the window is the whole run the answer is the union of.\<close>

text \<open>One step: the oldest pending time point's answer is its abstract entry's.\<close>

text \<open>The shift pops the pending time points that no later one can affect, in order.\<close>

end
(*>*)
