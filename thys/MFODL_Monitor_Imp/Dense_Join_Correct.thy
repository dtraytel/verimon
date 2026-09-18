(*<*)
theory Dense_Join_Correct
  imports Dense_Imp Imap_Correct
begin
(*>*)

section \<open>The dense join's heap index, in separation logic\<close>

text \<open>
  @{theory MFODL_Monitor_Imp.Imap_Correct} verifies the table the index is built on.  On top of
  it the three loops of @{const dbin_join_h} are ordinary list inductions: the index holds the
  smaller side, keyed by its projection onto the shared columns, and the larger side probes it.

  The pure @{const dindex} is the same index as a @{type mapping}, and @{const dprobe_step} and
  @{const dprobe_step_l} are the same probe steps, so each loop's specification says that it
  computes what the pure one does.  @{const dgen_join} is already proved to be the join
  (@{thm [source] dgen_join_eq}), which is what carries the result back to @{const dbin_join}.
\<close>

subsection \<open>Building the index\<close>

lemma lookup_dindex_step:
  "Mapping.lookup (dindex_step msk x mp)
   = (Mapping.lookup mp)(dproj msk x \<mapsto> (case Mapping.lookup mp (dproj msk x) of
        None \<Rightarrow> [x] | Some l \<Rightarrow> x # l))"
  by (auto simp: dindex_step_def Let_def Mapping.lookup_update' fun_eq_iff split: option.splits)

lemma lookup_Mapping_empty[simp]: "Mapping.lookup Mapping.empty = Map.empty"
  by (simp add: fun_eq_iff Mapping.lookup_empty)

lemma didx_ins_rule:
  "<is_imap (Mapping.lookup mp) q>
     didx_ins msk xs q
   <\<lambda>q'. is_imap (Mapping.lookup (fold (dindex_step msk) xs mp)) q'>\<^sub>t"
proof (induct xs arbitrary: mp q)
  case Nil
  show ?case by (subst didx_ins.simps) sep_auto
next
  case (Cons x r)
  have eq: "(Mapping.lookup mp)(dproj msk x \<mapsto> (case Mapping.lookup mp (dproj msk x) of
      None \<Rightarrow> [x] | Some l \<Rightarrow> x # l)) = Mapping.lookup (dindex_step msk x mp)"
    by (simp add: lookup_dindex_step)
  show ?case
    by (subst didx_ins.simps)
       (sep_auto simp: eq heap: im_lookup_h_rule im_update_h_rule Cons)
qed

lemma didx_ins_empty_rule:
  "<is_imap Map.empty q>
     didx_ins msk (csorted_list_of_set T) q
   <\<lambda>q'. is_imap (Mapping.lookup (dindex msk T)) q'>\<^sub>t"
  using didx_ins_rule[where mp = Mapping.empty and msk = msk and xs = "csorted_list_of_set T"]
  by (simp add: dindex_def)

subsection \<open>Probing it\<close>

lemma dprobe_r_rule:
  "<is_imap (Mapping.lookup mp) q>
     dprobe_r p lk q xs acc
   <\<lambda>r. is_imap (Mapping.lookup mp) q * \<up>(r = fold (dprobe_step p lk mp) xs acc)>"
proof (induct xs arbitrary: acc)
  case Nil
  show ?case by (subst dprobe_r.simps) sep_auto
next
  case (Cons x r)
  show ?case
    by (subst dprobe_r.simps)
       (sep_auto simp: dprobe_step_def heap: im_lookup_h_rule Cons)
qed

lemma dprobe_l_rule:
  "<is_imap (Mapping.lookup mp) q>
     dprobe_l p rk q ys acc
   <\<lambda>r. is_imap (Mapping.lookup mp) q * \<up>(r = fold (dprobe_step_l p rk mp) ys acc)>"
proof (induct ys arbitrary: acc)
  case Nil
  show ?case by (subst dprobe_l.simps) sep_auto
next
  case (Cons y r)
  show ?case
    by (subst dprobe_l.simps)
       (sep_auto simp: dprobe_step_l_def heap: im_lookup_h_rule Cons)
qed

subsection \<open>The join\<close>

text \<open>
  Whichever side is indexed, the loop computes the pairs that agree on the shared columns,
  merged -- which is what @{thm [source] dgen_join_eq} says @{const dgen_join} is.  So the
  index's own choice of side, which is by list length rather than by cardinality and therefore
  need not agree with @{const dgen_join}'s, does not matter.
\<close>

lemma dprobe_r_dgen_join:
  assumes cA: "set (csorted_list_of_set A) = A" and cB: "set (csorted_list_of_set B) = B"
  shows "fold (dprobe_step p lk (dindex rk B)) (csorted_list_of_set A) empty_table
       = dgen_join p lk rk A B"
  unfolding dgen_join_eq[OF cA cB]
  by (auto simp: dprobe_fold dindex_lookup[OF cB] empty_table_def cA) force

lemma dprobe_l_dgen_join:
  assumes cA: "set (csorted_list_of_set A) = A" and cB: "set (csorted_list_of_set B) = B"
  shows "fold (dprobe_step_l p rk (dindex lk A)) (csorted_list_of_set B) empty_table
       = dgen_join p lk rk A B"
  unfolding dgen_join_eq[OF cA cB]
  by (auto simp: dprobe_l_fold dindex_lookup[OF cA] empty_table_def cB)

lemma dbin_join_h_rule:
  assumes cA: "set (csorted_list_of_set A) = A" and cB: "set (csorted_list_of_set B) = B"
  shows "<emp> dbin_join_h pl A pos B <\<lambda>r. \<up>(r = dbin_join pl A pos B)>\<^sub>t"
proof (cases pl)
  case (DJGen p lk rk)
  show ?thesis
  proof (cases "\<not> dense_heap_join \<or> \<not> pos \<or> Set.is_empty A \<or> Set.is_empty B")
    case True
    then show ?thesis unfolding DJGen by sep_auto
  next
    case False
    then have pos: "pos = True" and ne: "\<not> Set.is_empty A" "\<not> Set.is_empty B" by auto
    have pure: "dbin_join (DJGen p lk rk) A True B = dgen_join p lk rk A B"
      using ne by (simp add: dbin_join_def)
    show ?thesis
      unfolding DJGen
      using False
      by (sep_auto heap: im_new_rule didx_ins_empty_rule dprobe_r_rule dprobe_l_rule
          simp: pos pure dprobe_r_dgen_join[OF cA cB] dprobe_l_dgen_join[OF cA cB])
  qed
qed (sep_auto+)

corollary dbin_join_h_finite_rule:
  assumes "finite A" and "finite B"
  shows "<emp> dbin_join_h pl A pos B <\<lambda>r. \<up>(r = dbin_join pl A pos B)>\<^sub>t"
  by (rule dbin_join_h_rule) (simp_all add: set_csorted_list_of_set_etuple assms)

text \<open>
  So the heap index computes what @{const dbin_join} computes, whatever the flag
  @{const dense_heap_join} is set to and whichever side the length test picks -- which is what
  @{text \<open>-dense -heap_maps\<close>} needed and did not have.  The tables it is applied to are finite:
  every table the dense evaluator handles is, as @{theory MFODL_Monitor_Imp.Dense} establishes
  for the representation.
\<close>

subsection \<open>The multi-way conjunction\<close>

text \<open>
  Nearly every conjunction is compiled to a multi-way one, so the join is reached through
  @{const Dense_Imp.dmulti_join} rather than directly.  Its two loops carry the finiteness the
  join's rule asks for from one operand to the next.
\<close>

lemma finite_dgen_join:
  assumes A: "finite A" and B: "finite B"
  shows "finite (dgen_join p lk rk A B)"
proof -
  have "dgen_join p lk rk A B \<subseteq> (\<lambda>(a, b). dmerge p a b) ` (A \<times> B)"
    unfolding dgen_join_eq[OF set_csorted_list_of_set_etuple[OF A]
        set_csorted_list_of_set_etuple[OF B]]
    by auto
  then show ?thesis using A B by (auto intro: finite_subset)
qed

lemma finite_dbin_join[simp]:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (dbin_join pl A pos B)"
  by (cases pl)
     (auto simp: dbin_join_def dsemi_def empty_table_def intro: finite_dgen_join)

lemma finite_dands_pos:
  "finite t \<Longrightarrow> \<forall>u \<in> set us. finite u \<Longrightarrow> finite (dands_pos ps t us)"
proof (induct ps arbitrary: t us)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by (cases us) auto
qed

lemma dands_pos_h_rule:
  "finite t \<Longrightarrow> \<forall>u \<in> set us. finite u \<Longrightarrow>
   <emp> dands_pos_h ps t us <\<lambda>r. \<up>(r = dands_pos ps t us)>\<^sub>t"
proof (induct ps arbitrary: t us)
  case Nil
  show ?case by sep_auto
next
  case (Cons p ps)
  show ?case
  proof (cases us)
    case Nil
    then show ?thesis by sep_auto
  next
    case (Cons u us')
    then show ?thesis
      using Cons.prems
      by (sep_auto heap: dbin_join_h_finite_rule Cons.hyps)
  qed
qed

lemma dands_neg_h_rule:
  "finite t \<Longrightarrow> \<forall>u \<in> set us. finite u \<Longrightarrow>
   <emp> dands_neg_h ps t us <\<lambda>r. \<up>(r = dands_neg ps t us)>\<^sub>t"
proof (induct ps arbitrary: t us)
  case Nil
  show ?case by sep_auto
next
  case (Cons p ps)
  show ?case
  proof (cases us)
    case Nil
    then show ?thesis by sep_auto
  next
    case (Cons u us')
    then show ?thesis
      using Cons.prems
      by (sep_auto heap: dbin_join_h_finite_rule Cons.hyps)
  qed
qed

theorem dmulti_join_rule:
  assumes us: "\<forall>u \<in> set us. finite u"
  shows "<emp> Dense_Imp.dmulti_join ps ns us <\<lambda>r. \<up>(r = Dense.dmulti_join ps ns us)>\<^sub>t"
proof (cases us)
  case Nil
  then show ?thesis
    unfolding Nil Dense_Imp.dmulti_join_def Dense.dmulti_join_def by sep_auto
next
  case (Cons t r)
  have ft: "finite t" and fr: "\<forall>u \<in> set r. finite u" using us Cons by auto
  have ftk: "\<forall>u \<in> set (take (length ps) r). finite u" using fr by (auto dest: in_set_takeD)
  have fdr: "\<forall>u \<in> set (drop (length ps) r). finite u" using fr by (auto dest: in_set_dropD)
  have fp: "finite (dands_pos ps t (take (length ps) r))" by (rule finite_dands_pos[OF ft ftk])
  show ?thesis
    unfolding Cons Dense_Imp.dmulti_join_def Dense.dmulti_join_def
    by (sep_auto heap: dands_pos_h_rule[OF ft ftk] dands_neg_h_rule[OF fp fdr])
qed

text \<open>
  So the heap index computes what @{const Dense.dmulti_join} computes, whatever the flag
  @{const dense_heap_join} is set to and whichever side the length test picks -- which is what
  @{text \<open>-dense -heap_maps\<close>} needed and did not have.
\<close>

(*<*)
end
(*>*)
