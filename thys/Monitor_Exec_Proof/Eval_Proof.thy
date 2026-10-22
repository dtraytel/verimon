(*<*)
theory Eval_Proof
  imports "Monitor_Exec.Eval" Window_Dispatch_Proof Release_Window_Proof Trigger_Window_Proof Kernel_Call "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>
  Every theorem of @{theory MFODL_Monitor_Exec.Frame} needs its operand tables to be finite and
  well formed over the node's columns.  The simulation below takes that from the kernel: it is
  stated for the calls of @{const meval} that @{const kgood} covers, whose tables the kernel's
  correctness theorem describes (@{thm [source] kgood_tables}).
\<close>

text \<open>
  @{term "esim n ks cs tw \<phi>d \<phi>"} relates a executable formula to a kernel one whose tables are over
  the column list @{term ks}, read by the executable one over its ascending order @{term cs}.  The
  relation is about the state alone; the operand well-formedness that the
  @{theory MFODL_Monitor_Exec.Frame} theorems ask for comes from the call (@{const kgood}).
\<close>

text \<open>Widening the bound is harmless, which is what the node needs when a new batch of
  timestamps arrives.\<close>

text \<open>A fresh batch of operand tables and timestamps enters the buffer at both representations at
  once.  The batch's timestamps are all at or after the old bound, and the buffer's are all at or
  before it, so the concatenation stays sorted and the new bound is the batch's last timestamp.\<close>

text \<open>
  One firing of the Until node: the buffer traversal steps the two structures in lockstep, and
  then one evaluation at the timestamp the traversal reports yields the reordering of what the
  kernel's one yields.
\<close>

subsection \<open>The release structure at the ascending frame\<close>

text \<open>
  The release node steps its structure through the buffer like the Until node, with the
  timestamp-indexed relation, and reads it with @{const eraux_eval}, which pops the same entries
  as @{const eval_until} pops from the list the structure stands for.
\<close>

text \<open>One firing of the trigger structure: the buffer traversal that steps it once per pending
  timestamp and collects what it answers.  The two runs stay in step by
  @{thm [source] mbuf2T_take_rel}, and each individual step is @{thm [source] etw_update}
  followed by @{thm [source] etw_result}.\<close>

text \<open>The outer buffer's two sides are therefore related rather than mapped, so the traversal
  that drains it needs a relational counterpart of @{thm [source] mbuf2_take_map}.\<close>

text \<open>One firing of the fused node's trigger structure.  It differs from the standalone node's
  only in what each step appends: the kernel keeps the read's column list beside its table, and
  the executable side keeps the empty window as @{term None}.\<close>

text \<open>The executable tables are read at the frozen predicate's variables through their own
  columns: reading a tuple's restriction there is reading the tuple.\<close>

text \<open>The fact the relation is designed to hand out at every node.\<close>

section \<open>The simulation\<close>

subsection \<open>The multi-way buffer of reordered tables\<close>

text \<open>The timestamped take, which the two match nodes use, keeps the buffers related in the same
  way; the accumulator is a parameter here because the past node threads a pair of the reported
  tables and the structure, and the future node the structure alone.\<close>

subsection \<open>The queues the nodes keep\<close>

text \<open>A node keeps its buffers in queues, and the relation is stated on the lists they represent.
  Each queue operation commutes with the representation, so a step of a queue is a step of the
  list it represents.\<close>

subsection \<open>Stepping a list of operands\<close>

text \<open>
  The operand block shared by the multi-operand nodes: given the induction hypotheses for the
  operands, their executable steps report the reordered tables, stay related, and the buffer
  stays related after adding their results.
\<close>

subsection \<open>One firing of the Since structure\<close>

text \<open>
  One firing of @{const meval_since} on the executable side reports the same windows as one firing on
  the kernel's, and the relation is preserved.  The recursion is driven by the buffer alone, so
  the two sides step in lockstep; the induction is over the kernel's own recursion.
\<close>

text \<open>
  The simulation itself.  Every case is one theorem of @{theory MFODL_Monitor_Exec.Frame}
  applied pointwise to the operand's output list, with @{thm [source] kgood_tables} supplying
  the operand well-formedness: the operands' calls are good when the node's is.
\<close>

text \<open>
  The induction is over the derivation of the simulation, which gives the statement for an
  operand's own derivation.  A node that re-enters the evaluator on an operand's \<^emph>\<open>successor\<close>
  state -- the freeze does -- needs it for a derivation that is not a sub-derivation, so the
  statement carries a bound \<open>NN\<close> on the formula's size and an assumption \<open>Q\<close> giving
  it below that bound.  \<open>esim_deval_bound\<close> closes the loop by induction on the
  bound, and \<open>esim_deval\<close> instantiates it.
\<close>

text \<open>
  A let-bound formula's tables are reordered by the kernel from the formula's columns to the
  positional ones before they enter the database.  The executable formula's are already over the
  positional columns, which are the ascending order of the same set, so the executable table
  \<^emph>\<open>is\<close> the reordered one and the two databases are literally the same.\<close>

text \<open>
  The recursive let runs its bound formula against databases it builds itself, feeding the
  previous round's output back under the bound predicate.  The two runs produce literally the
  same lists, so their states stay in step round by round.  The guard that rejects a round in
  which the formula's size changed never fires on either side, because neither evaluator changes
  its formula's size.
\<close>

text \<open>One firing of the multi-way join: the operands at their own columns, split into the
  positive and the negative ones, as @{thm [source] gmulti_join_eq} takes them.\<close>

text \<open>One firing of a fused aggregating Since node.  The node reports the aggregated windows,
  read through its guard; the kernel's node reports the windows, which its aggregation then
  aggregates.\<close>

text \<open>One firing of a Since node, whatever the post-processing of its window: the executable
  node's results are the kernel's under the window's post-processing, and the relation carries
  over to the successor states.\<close>

text \<open>One firing of an Until node, likewise.\<close>

text \<open>Induction on the bound discharges the assumption the theorem above carries, and
  instantiating it at the formula's own size recovers the statement without it.\<close>

end
(*>*)
