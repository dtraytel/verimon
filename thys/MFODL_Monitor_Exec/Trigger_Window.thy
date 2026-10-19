(*<*)
theory Trigger_Window
  imports Until_Gen
begin
(*>*)

section \<open>Trigger: interval side conditions and the read\<close>

text \<open>A table is used throughout with the two properties every theorem about the executable
  representation needs of it: it is well formed over its columns, and it is finite.\<close>

abbreviation (input) ftable :: "nat list \<Rightarrow> 'a table \<Rightarrow> bool" where
  "ftable A X \<equiv> table A X \<and> finite X"

lemma emsk_args_distinct_R: "emsk_args args msk \<Longrightarrow> distinct (args_R args)"
  by (simp add: emsk_args_def strict_sorted_iff)


subsection \<open>The interval side condition\<close>

text \<open>
  The executable trigger structure (theory @{text Trigger_Swag}) answers for the kernel's
  auxiliary list under the side condition @{term tok} on the operand frames: the standalone
  trigger meets it by its interval containing zero, the fused And-Trigger by its two operand
  frames agreeing and its left operand being positive.  Without zero in the interval the time
  points that are not yet in it contribute their left tables to the read, which is a table only
  when the left operand has the node's columns.
\<close>

definition tok :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> bool" where
  "tok cR cL args \<longleftrightarrow> mem (args_ivl args) 0 \<or> (cL = cR \<and> args_pos args)"

lemma tok_mem0: "mem (args_ivl args) 0 \<Longrightarrow> tok cR cL args"
  by (simp add: tok_def)

subsection \<open>The read is a finite table\<close>

text \<open>The read of the trigger structure is a finite table over the right operand's columns.
  With an interval containing zero that is immediate, because the window then always holds the
  latest time point and the read is contained in its right table.  Without it a safe trigger has
  the same columns on both sides, and the read is contained in the union of the window's
  tables -- which is what the weakened form below states.\<close>

lemma ftable_trigger_results:
  fixes args :: args
  assumes wf: "\<forall>(t, l, r) \<in> set auxlist. ftable L l \<and> ftable R r"
    and ne: "auxlist \<noteq> []" and m0: "mem (args_ivl args) 0"
    and lst: "fst (last auxlist) = cur" and aR: "args_R args = R"
  shows "ftable R (snd (trigger_results args cur auxlist))"
    and "fst (trigger_results args cur auxlist) = R"
proof -
  have kl: "length auxlist - 1 < length auxlist" using ne by simp
  obtain l0 r0 where a0: "auxlist ! (length auxlist - 1) = (cur, l0, r0)"
    using lst ne by (cases "auxlist ! (length auxlist - 1)") (simp add: last_conv_nth)
  have mem0: "auxlist ! (length auxlist - 1) \<in> set auxlist" using kl by (rule nth_mem)
  have tr0: "ftable R r0" using wf mem0 a0 by force
  have mm: "mem (args_ivl args) (cur - cur)" using m0 by simp
  have m: "(cur, l0, r0) \<in> set auxlist" using mem0 a0 by simp
  have fl: "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist \<noteq> []"
  proof
    assume e: "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist = []"
    have "\<forall>x \<in> set auxlist. \<not> (case x of (t, _, _) \<Rightarrow> mem (args_ivl args) (cur - t))"
      using e unfolding filter_empty_conv by simp
    from this[rule_format, OF m] show False using mm by simp
  qed
  have tb: "table R (snd (trigger_results args cur auxlist))"
    using fl aR by (auto simp: table_def)
  have sub: "snd (trigger_results args cur auxlist) \<subseteq> r0"
  proof
    fix tu assume tu: "tu \<in> snd (trigger_results args cur auxlist)"
    have H: "\<forall>i \<in> {0..<length auxlist}. case auxlist ! i of (t, l, r) \<Rightarrow>
        mem (args_ivl args) (cur - t) \<longrightarrow>
        (tu \<in> r \<or> (\<exists>j \<in> {i<..<length auxlist}.
           join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
             (restrict (args_L args) (args_R args) tu)))"
      using tu fl by simp
    have "{length auxlist - 1<..<length auxlist} = {}" using ne by auto
    then show "tu \<in> r0" using H[rule_format, of "length auxlist - 1"] kl a0 mm by simp
  qed
  have fin: "finite (snd (trigger_results args cur auxlist))"
    by (rule finite_subset[OF sub]) (use tr0 in simp)
  show "ftable R (snd (trigger_results args cur auxlist))" using tb fin by simp
  show "fst (trigger_results args cur auxlist) = R" using fl aR by simp
qed

lemma ftable_trigger_results_weak:
  fixes args :: args
  assumes wf: "\<forall>(t, l, r) \<in> set auxlist. ftable L l \<and> ftable R r"
    and ne: "auxlist \<noteq> []" and lst: "fst (last auxlist) = cur"
    and aL: "args_L args = L" and aR: "args_R args = R" and dR: "distinct R"
    and wkc: "mem (args_ivl args) 0 \<or> (args_pos args \<and> set L = set R)"
  shows "ftable (fst (trigger_results args cur auxlist)) (snd (trigger_results args cur auxlist)) \<and>
    (fst (trigger_results args cur auxlist) = R \<or> fst (trigger_results args cur auxlist) = [])"
proof (cases "mem (args_ivl args) 0")
  case True
  show ?thesis using ftable_trigger_results[OF wf ne True lst aR] by simp
next
  case False
  then have pos: "args_pos args" and LR: "set L = set R" using wkc by auto
  show ?thesis
  proof (cases "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist = []")
    case True
    then show ?thesis by (simp add: table_def unit_table_def wf_tuple_def)
  next
    case False
    then obtain x where x: "x \<in> set auxlist"
      and px: "case x of (t, _, _) \<Rightarrow> mem (args_ivl args) (cur - t)"
      by (auto simp: filter_empty_conv)
    obtain t0 l0 r0 where x0: "x = (t0, l0, r0)" by (cases x)
    have mm: "mem (args_ivl args) (cur - t0)" using px x0 by simp
    obtain i0 where i0: "i0 < length auxlist" and xi: "auxlist ! i0 = (t0, l0, r0)"
      using x x0 by (auto simp: in_set_conv_nth)
    have fl: "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist)"
      using False by simp
    have tr0: "ftable R r0" using wf x x0 by force
    have tb: "table R (snd (trigger_results args cur auxlist))"
      using fl aR by (auto simp: table_def)
    have sub: "snd (trigger_results args cur auxlist)
        \<subseteq> r0 \<union> (\<Union>j \<in> {0..<length auxlist}. restrict R L ` (fst \<circ> snd) (auxlist ! j))"
    proof
      fix tu assume tu: "tu \<in> snd (trigger_results args cur auxlist)"
      have wt: "wf_tuple R tu" using tu fl aR by simp
      have pj: "restrict R L (restrict (args_L args) (args_R args) tu) = tu"
        using restrict_restrict[of R L R tu] restrict_idle[OF dR wt] aL aR LR by simp
      have H: "\<forall>i \<in> {0..<length auxlist}. case auxlist ! i of (t, l, r) \<Rightarrow>
          mem (args_ivl args) (cur - t) \<longrightarrow>
          (tu \<in> r \<or> (\<exists>j \<in> {i<..<length auxlist}.
             join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
               (restrict (args_L args) (args_R args) tu)))"
        using tu fl by simp
      have step: "tu \<in> r0 \<or> (\<exists>j \<in> {i0<..<length auxlist}.
          join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
            (restrict (args_L args) (args_R args) tu))"
        using H[rule_format, of i0] i0 xi mm by simp
      show "tu \<in> r0 \<union> (\<Union>j \<in> {0..<length auxlist}. restrict R L ` (fst \<circ> snd) (auxlist ! j))"
        using step pos by (auto intro: image_eqI[where f = "restrict R L", OF pj[symmetric]])
    qed
    have finl: "finite (\<Union>j \<in> {0..<length auxlist}. restrict R L ` (fst \<circ> snd) (auxlist ! j))"
    proof (rule finite_UN_I[OF finite_atLeastLessThan])
      fix j assume "j \<in> {0..<length auxlist}"
      then have m: "auxlist ! j \<in> set auxlist" by simp
      obtain vj lj rj where e: "auxlist ! j = (vj, lj, rj)" by (cases "auxlist ! j")
      show "finite (restrict R L ` (fst \<circ> snd) (auxlist ! j))" using wf m unfolding e by force
    qed
    have fin: "finite (snd (trigger_results args cur auxlist))"
      by (rule finite_subset[OF sub]) (use tr0 finl in simp)
    show ?thesis using tb fin fl aR by simp
  qed
qed

(*<*)
end
(*>*)