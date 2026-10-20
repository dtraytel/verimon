(*<*)
theory IEval
  imports Eval ITable
begin
(*>*)

section \<open>The executable evaluator over indexed tables\<close>

text \<open>
  The evaluator below is @{const eeval} with the tables of the unions' and joins' buffers
  indexed (@{typ "event_data itab"}): a join probes the index an operand carries at the plan's
  mask instead of building one (@{const ijoin}), and a union keeps its left operand's indices.
  The other nodes see plain tables, and the freeze and the recursive let run @{const eeval} on
  their subtree.  Forgetting the indices (@{const eabs}) maps a run of this evaluator to a run of
  @{const eeval} (@{text ieval_eeval}), so the simulation of the kernel and its correctness carry
  over unchanged.
\<close>

type_synonym itable = "event_data itab"
type_synonym iebuf2 = "itable mbuf_t \<times> itable mbuf_t"
type_synonym ieformula =
  "(iebuf2, uebufn, event_data table mbuf_t \<times> event_data table option mbuf_t) geformula"

lift_definition mbuf_t_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mbuf_t \<Rightarrow> 'b mbuf_t" is map .

lemma Rep_mbuf_t_map[simp]: "Rep_mbuf_t (mbuf_t_map f b) = map f (Rep_mbuf_t b)"
  by transfer simp

lemma mbuf_t_map_comp[simp]: "mbuf_t_map f (mbuf_t_map g b) = mbuf_t_map (f \<circ> g) b"
  by transfer simp

lemma mbuf_t_map_id[simp]: "mbuf_t_map (\<lambda>x. x) b = b" "mbuf_t_map id b = b"
  by (transfer, simp)+

definition ib2 :: "iebuf2 \<Rightarrow> uebuf2" where
  "ib2 = map_prod (mbuf_t_map iset) (mbuf_t_map iset)"

definition eb2 :: "uebuf2 \<Rightarrow> iebuf2" where
  "eb2 = map_prod (mbuf_t_map itab) (mbuf_t_map itab)"

lemma ib2_eb2[simp]: "ib2 (eb2 b) = b"
  by (cases b) (simp add: ib2_def eb2_def comp_def)

definition eabs :: "ieformula \<Rightarrow> eformula" where
  "eabs = map_geformula ib2 id id"

definition eemb :: "eformula \<Rightarrow> ieformula" where
  "eemb = map_geformula eb2 id id"

lemma eabs_eemb[simp]: "eabs (eemb \<phi>) = \<phi>"
  by (simp add: eabs_def eemb_def geformula.map_comp comp_def geformula.map_ident)

end
