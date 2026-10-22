(*<*)
theory Compile_Proof
  imports "Monitor_Exec.Compile" Correct_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>The structures the compiler starts the nodes with, read through their representations.\<close>

lemma rdsx_udsx_init[simp]: "rdsx (udsx_init args msk) = esx_init args msk"
  by (rule esx_init_rdsx[symmetric])

lemma rdux_udux_init[simp]: "rdux (udux_init args) = eux_init args"
  by (rule eux_init_rdux[symmetric])

lemma rdux_udux_init_agg[simp]: "rdux (udux_init_agg args p) = eux_init_agg args p"
  by (rule eux_init_agg_rdux[symmetric])

subsection \<open>Column lists in ascending order\<close>

lemma set_ecols[simp]: "set (ecols k) = set k"
  by (simp add: ecols_def set_cols)

lemma ecols_Nil[simp]: "ecols [] = []"
  by (simp add: ecols_def set_cols_empty)

subsection \<open>The kernel's initial state\<close>

text \<open>The fields of the kernel's initial state, read off @{const minit_safe}.\<close>

subsection \<open>The nodes the executable fragment does not cover\<close>

text \<open>
  @{const eof} is total, and answers @{const EFail} where it has no executable node or where a check
  fails.  Nothing relates @{const EFail} to a kernel formula, so every statement below is
  conditional on the compiled formula containing none of them -- @{term "eofz n \<phi>"} -- and each
  check of the compiler is then available as a fact.
\<close>

text \<open>A safe formula's initial state is a constant table only for an equality, whose table the
  kernel's correctness proof describes.\<close>

subsection \<open>The temporal structures' initial states\<close>

subsection \<open>Aggregations\<close>

subsection \<open>The guard\<close>

text \<open>A constraint over a node goes into the node as its guard exactly when the node is a fused
  aggregating Since without one; the node is then related to the kernel's constraint over the
  kernel's node by the rule for the guarded Since, and otherwise the constraint stays above it.\<close>

subsection \<open>The compiler produces a simulation\<close>

context verimon_spec
begin

end

end
