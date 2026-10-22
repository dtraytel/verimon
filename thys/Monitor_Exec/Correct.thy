(*<*)
theory Correct
  imports IEval
begin
(*>*)



subsection \<open>The executable state machine\<close>

text \<open>
  The executable monitor's online interface mirrors the kernel's -- the record \<open>mstate\<close> and the
  function \<open>mstep\<close> -- field for field, with @{const ieval} in place of @{const meval}.  The state
  additionally records the ascending column list its verdicts are narrowed to, and its formula
  is the indexed one: the state relation forgets the indices (@{const eabs}) and relates the
  result to the kernel's formula by @{const esim}, and @{thm [source] ieval_eeval} carries a step
  of @{const ieval} over to one of @{const eeval}.
\<close>

record emstate =
  emstate_i :: nat
  emstate_j :: nat
  emstate_m :: ieformula
  emstate_n :: nat
  emstate_cs :: cols
  emstate_t :: "ts mbuf_t"

text \<open>
  One field is not the kernel's.  The kernel keeps the timestamps whose verdict is still
  outstanding in a list, and at every step appends the new one to its end and drops the ones it
  has just reported.  Both are linear in the list, and the list is as long as the window of the
  outermost future operator.  The executable state keeps the same sequence in an @{typ "'a mbuf_t"},
  which \<open>is\<close> a list -- the type is a copy of @{typ "'a list"} and @{const Rep_mbuf_t} the copy's
  isomorphism -- so the state relation and this theory's proofs say what they would say for a
  list.  What changes is the code: @{typ "'a mbuf_t"} is implemented by a queue, where an append
  and a head removal are amortised constant.  The step takes the timestamps off the front one at
  a time, with @{const mbuf_t_cases}.
\<close>

text \<open>
  Pairing one step's verdicts with the timestamps they belong to.  Where the buffer runs out the
  index still advances by the number of verdicts, which is what the kernel's @{term "length xs"}
  does.
\<close>

fun eannotate :: "nat \<Rightarrow> ts mbuf_t \<Rightarrow> 'a list \<Rightarrow> (nat \<times> ts \<times> 'a) list \<Rightarrow>
    nat \<times> ts mbuf_t \<times> (nat \<times> ts \<times> 'a) list" where
  "eannotate i tq [] acc = (i, tq, rev acc)"
| "eannotate i tq (v # vs) acc = (case mbuf_t_cases tq of
      (None, tq') \<Rightarrow> (i + 1 + length vs, tq', rev acc)
    | (Some t, tq') \<Rightarrow> eannotate (i + 1) tq' vs ((i, t, v) # acc))"

definition emstep :: "database \<times> ts \<Rightarrow> emstate \<Rightarrow>
    (nat \<times> ts \<times> event_data table) list \<times> emstate" where
  "emstep tdb st =
    (case ieval [] (emstate_j st + 1) [snd tdb] (demb (fst tdb)) (emstate_m st) of
      (xs, m) \<Rightarrow>
      (case eannotate (emstate_i st) (emstate_t st @@ [snd tdb]) (map iset xs) [] of
        (i', tq, vs) \<Rightarrow> (vs,
        \<lparr> emstate_i = i',
          emstate_j = emstate_j st + 1,
          emstate_m = m,
          emstate_n = emstate_n st,
          emstate_cs = emstate_cs st,
          emstate_t = tq \<rparr>)))"

primrec emsteps0_stateless where
  "emsteps0_stateless [] st = []"
| "emsteps0_stateless (tdb # \<pi>) st =
    (let (V', st') = emstep (apfst mk_db tdb) st in V' @ emsteps0_stateless \<pi> st')"

lift_definition emsteps_stateless :: "Formula.prefix \<Rightarrow> emstate \<Rightarrow>
    (nat \<times> ts \<times> event_data table) list" is emsteps0_stateless .

definition emonitor :: "emstate \<Rightarrow> Formula.prefix \<Rightarrow> (nat \<times> ts \<times> event_data table) list" where
  "emonitor st \<pi> = emsteps_stateless \<pi> st"

definition eindex :: "ipolicy \<Rightarrow> emstate \<Rightarrow> emstate" where
  "eindex ix st = st\<lparr>emstate_m := eemb ix [] (eabs (emstate_m st))\<rparr>"

context verimon_spec
begin

end

(*<*)
end
(*>*)
