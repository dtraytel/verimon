(*<*)
theory Monitor_Code_Imp
  imports Monitor_Imp Monitor_Imp2 Dense_Imp Dense_Code_Opt
    "MFODL_Monitor_Dense.Dense_Descend_Code" "MFODL_Monitor_Dense.Dense_Unbox_Exec"
    "MFODL_Monitor_Devel.Monitor_Code"
begin
(*>*)

text \<open>
  The code export replaces the one of @{theory MFODL_Monitor_Devel.Monitor_Code}: the only
  monitor exported is the one over the tuples without their empty columns.
  @{const minit_safe_d} builds its initial state -- compiling the sparse formula into the dense
  one and allocating a hash table for every Since structure that takes one -- and
  @{const mstep_d} performs one step on it.  Both are heap computations; the generated OCaml
  represents them as thunks that the front end applies once per time point, in order (see
  @{theory MFODL_Monitor_Imp.Monitor_Imp}).

  Nothing else is exported, so the evaluation functions over the wide tuples -- the pure one of
  @{theory MFODL_Monitor_Devel.Monitor_Impl} and the two heap-resident ones of
  @{theory MFODL_Monitor_Imp.Monitor_Imp} and @{theory MFODL_Monitor_Imp.Monitor_Imp2} -- are
  unreachable, and the code generator drops them together with the operations on wide tables
  that only they used.  What the front end still shares with them is its own view of a formula
  (@{const convert_multiway}, @{const mmonitorable_exec}, @{const type_check}) and the sparse
  formula @{const meinit0} builds, which is what the dense compiler descends.
\<close>

text \<open>
  Imperative HOL prints the monad's bind as a two-argument lambda applied to one argument,
  @{text "(fun f_ () -> f_ (m ()) ()) f"}, which OCaml compiles as a partial application: two
  closures for every bind.  On the join of @{text "A(x,y) AND (ONCE[0,20] B(y,z))"} that is 104
  million words, a third of everything the join allocates.  Printing it as
  @{text "(fun () -> f (m ()) ())"} leaves one closure, and the placeholders of a printing are
  filled in argument order, so the flipped @{const bind_flip} is what carries it.

  The declaration belongs here rather than next to that definition: this theory merges the
  branch that carries it with the one that carries Imperative HOL's own, and the merge keeps
  the original unless it is superseded in the theory that exports the code.
\<close>

code_printing constant Heap_Monad.bind \<rightharpoonup> (OCaml)
| constant bind_flip \<rightharpoonup> (OCaml) "(fun/ ()/ ->/ (_)/ ((_)/ ())/ ())"

declare bind_flip_code[code]

text \<open>
  The verified dense evaluator of @{theory MFODL_Monitor_Dense.Dense_Eval}, wrapped in the same
  online interface the kernel has, so that it can be measured next to the two it sits between:
  the kernel's own evaluator, which it is proved to simulate, and the executable dense one,
  which refines it further with short tuples and heap-resident structures.  It is a pure
  function over the kernel's wide tables, so the database operations of the wide representation
  come back for it -- but not the kernel's evaluator, which it no longer calls at any node.
  @{const vdfail_nodes} says whether the compiler covered the whole formula; it must be zero for
  the correctness theorem to apply, and the front end refuses the formula otherwise.
\<close>

text \<open>@{thm [source] mestate_def} is the kernel's code constructor for its state record, so the
  selectors the dense initialiser reads need their equations stated against it; the record's own
  are about a constructor the code generator does not have.\<close>

lemma mstate_sel_code[code]:
  "mstate_i (mestate i j m n t \<zeta>) = i"
  "mstate_j (mestate i j m n t \<zeta>) = j"
  "mstate_m (mestate i j m n t \<zeta>) = m"
  "mstate_n (mestate i j m n t \<zeta>) = n"
  "mstate_t (mestate i j m n t \<zeta>) = linearize t"
  by (simp_all add: mestate_def)

definition dminit_safe :: "ty Formula.formula \<Rightarrow> dmstate" where
  "dminit_safe \<phi> = dof_state (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) (minit_safe \<phi>)"

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval RBT_set Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*the front end's own functions on formulas*)
  convert_multiway mmonitorable_exec type_check
  (*the monitor and its database, both over the tuples without their empty columns*)
  minit_safe_d mstep_d dfail_nodes
  utable_of_list uempty_db uinsert_table_into_db urbt_fold
  (*the verified dense monitor, over the short tuples*)
  udminit_safe udmstep uvdfail_nodes udmstate_m
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
