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

  The pure @{const gindex} is the same index as a @{type mapping}, and @{const gprobe_step} and
  @{const gprobe_step_l} are the same probe steps, so each loop's specification says that it
  computes what the pure one does.  @{const ggen_join} is already proved to be the join
  (@{thm [source] ggen_join_spec}), which is what carries the result back to @{const gbin_join}.
\<close>

subsection \<open>Building the index\<close>

lemma lookup_dindex_step:
  "Mapping.lookup (gindex_step msk x mp)
   = (Mapping.lookup mp)(dproj msk x \<mapsto> (case Mapping.lookup mp (dproj msk x) of
        None \<Rightarrow> [x] | Some l \<Rightarrow> x # l))"
  by (auto simp: gindex_step_def Let_def Mapping.lookup_update' fun_eq_iff split: option.splits)

lemma lookup_Mapping_empty[simp]: "Mapping.lookup Mapping.empty = Map.empty"
  by (simp add: fun_eq_iff Mapping.lookup_empty)

lemma didx_ins_rule:
  "<ided.is_imap (Mapping.lookup mp) q>
     didx_ins msk xs q
   <\<lambda>q'. ided.is_imap (Mapping.lookup (fold (gindex_step msk) xs mp)) q'>\<^sub>t"
proof (induct xs arbitrary: mp q)
  case Nil
  show ?case by (subst didx_ins.simps) sep_auto
next
  case (Cons x r)
  have eq: "(Mapping.lookup mp)(dproj msk x \<mapsto> (case Mapping.lookup mp (dproj msk x) of
      None \<Rightarrow> [x] | Some l \<Rightarrow> x # l)) = Mapping.lookup (gindex_step msk x mp)"
    by (simp add: lookup_dindex_step)
  show ?case
    by (subst didx_ins.simps)
       (sep_auto simp: eq heap: ided.im_lookup_h_rule ided.im_update_h_rule Cons)
qed

lemma didx_ins_empty_rule:
  "<ided.is_imap Map.empty q>
     didx_ins msk (csl T) q
   <\<lambda>q'. ided.is_imap (Mapping.lookup (gindex msk T)) q'>\<^sub>t"
  using didx_ins_rule[where mp = Mapping.empty and msk = msk and xs = "csl T"]
  by (simp add: gindex_def)

subsection \<open>Probing it\<close>

lemma dprobe_r_rule:
  "<ided.is_imap (Mapping.lookup mp) q>
     dprobe_r p lk q xs acc
   <\<lambda>r. ided.is_imap (Mapping.lookup mp) q * \<up>(r = fold (gprobe_step p lk mp) xs acc)>"
proof (induct xs arbitrary: acc)
  case Nil
  show ?case by (subst dprobe_r.simps) sep_auto
next
  case (Cons x r)
  show ?case
    by (subst dprobe_r.simps)
       (sep_auto simp: gprobe_step_def heap: ided.im_lookup_h_rule Cons)
qed

lemma dprobe_l_rule:
  "<ided.is_imap (Mapping.lookup mp) q>
     dprobe_l p rk q ys acc
   <\<lambda>r. ided.is_imap (Mapping.lookup mp) q * \<up>(r = fold (gprobe_step_l p rk mp) ys acc)>"
proof (induct ys arbitrary: acc)
  case Nil
  show ?case by (subst dprobe_l.simps) sep_auto
next
  case (Cons y r)
  show ?case
    by (subst dprobe_l.simps)
       (sep_auto simp: gprobe_step_l_def heap: ided.im_lookup_h_rule Cons)
qed

subsection \<open>The join\<close>

text \<open>
  Whichever side is indexed, the loop computes the pairs that agree on the shared columns,
  merged -- which is what @{thm [source] ggen_join_spec} says @{const ggen_join} is.  So the
  index's own choice of side, which is by list length rather than by cardinality and therefore
  need not agree with @{const ggen_join}'s, does not matter.
\<close>

lemma dprobe_r_dgen_join:
  assumes cA: "set (csl A) = A" and cB: "set (csl B) = B"
  shows "fold (gprobe_step p lk (gindex rk B)) (csl A) {}
       = ggen_join p lk rk A B"
  unfolding ggen_join_spec[OF cA cB]
  by (auto simp: gprobe_fold gindex_lookup[OF cB] empty_table_def cA) force

lemma dprobe_l_dgen_join:
  assumes cA: "set (csl A) = A" and cB: "set (csl B) = B"
  shows "fold (gprobe_step_l p rk (gindex lk A)) (csl B) {}
       = ggen_join p lk rk A B"
  unfolding ggen_join_spec[OF cA cB]
  by (auto simp: gprobe_l_fold gindex_lookup[OF cA] empty_table_def cB)

lemma dbin_join_h_rule:
  assumes cA: "set (csl A) = A" and cB: "set (csl B) = B"
  shows "<emp> dbin_join_h pl A pos B <\<lambda>r. \<up>(r = gbin_join pl A pos B)>\<^sub>t"
proof (cases pl)
  case (DJGen p lk rk)
  show ?thesis
  proof (cases "\<not> dense_heap_join \<or> \<not> pos \<or> Set.is_empty A \<or> Set.is_empty B")
    case True
    then show ?thesis unfolding DJGen by sep_auto
  next
    case False
    then have pos: "pos = True" and ne: "\<not> Set.is_empty A" "\<not> Set.is_empty B" by auto
    have pure: "gbin_join (DJGen p lk rk) A True B = ggen_join p lk rk A B"
      using ne by (simp add: gbin_join_def)
    show ?thesis
      unfolding DJGen
      using False
      by (sep_auto heap: ided.im_new_rule didx_ins_empty_rule dprobe_r_rule dprobe_l_rule
          simp: pos pure dprobe_r_dgen_join[OF cA cB] dprobe_l_dgen_join[OF cA cB])
  qed
qed (sep_auto+)

corollary dbin_join_h_finite_rule:
  assumes "finite A" and "finite B"
  shows "<emp> dbin_join_h pl A pos B <\<lambda>r. \<up>(r = gbin_join pl A pos B)>\<^sub>t"
  by (rule dbin_join_h_rule) (simp_all add: set_csl_ed assms)

text \<open>
  So the heap index computes what @{const gbin_join} computes, whatever the flag
  @{const dense_heap_join} is set to and whichever side the length test picks -- which is what
  @{text \<open>-dense -heap_maps\<close>} needed and did not have.  The tables it is applied to are finite:
  every table the dense evaluator handles is, as @{theory MFODL_Monitor_Dense.Dense} establishes
  for the representation.
\<close>

subsection \<open>The multi-way conjunction\<close>

text \<open>
  Nearly every conjunction is compiled to a multi-way one, so the join is reached through
  @{const Dense_Imp.dmulti_join} rather than directly.  Its two loops carry the finiteness the
  join's rule asks for from one operand to the next.
\<close>

lemma finite_dgen_join:
  assumes A: "finite (A :: event_data list set)" and B: "finite B"
  shows "finite (ggen_join p lk rk A B)"
proof -
  have "ggen_join p lk rk A B \<subseteq> (\<lambda>(a, b). dmerge p a b) ` (A \<times> B)"
    unfolding ggen_join_spec[OF set_csl_ed[OF A] set_csl_ed[OF B]]
    by auto
  then show ?thesis using A B by (auto intro: finite_subset)
qed

lemma finite_dbin_join[simp]:
  "finite (A :: event_data list set) \<Longrightarrow> finite B \<Longrightarrow> finite (gbin_join pl A pos B)"
  by (cases pl)
     (auto simp: gbin_join_def dsemi_def empty_table_def intro: finite_dgen_join)

lemma finite_dands_pos:
  "finite (t :: event_data list set) \<Longrightarrow> \<forall>u \<in> set us. finite u \<Longrightarrow> finite (gands_pos ps t us)"
proof (induct ps arbitrary: t us)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by (cases us) auto
qed

lemma dands_pos_h_rule:
  "finite t \<Longrightarrow> \<forall>u \<in> set us. finite u \<Longrightarrow>
   <emp> dands_pos_h ps t us <\<lambda>r. \<up>(r = gands_pos ps t us)>\<^sub>t"
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
   <emp> dands_neg_h ps t us <\<lambda>r. \<up>(r = gands_neg ps t us)>\<^sub>t"
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
  shows "<emp> Dense_Imp.dmulti_join ps ns us <\<lambda>r. \<up>(r = gmulti_join ps ns us)>\<^sub>t"
proof (cases us)
  case Nil
  then show ?thesis
    unfolding Nil Dense_Imp.dmulti_join_def gmulti_join_def by sep_auto
next
  case (Cons t r)
  have ft: "finite t" and fr: "\<forall>u \<in> set r. finite u" using us Cons by auto
  have ftk: "\<forall>u \<in> set (take (length ps) r). finite u" using fr by (auto dest: in_set_takeD)
  have fdr: "\<forall>u \<in> set (drop (length ps) r). finite u" using fr by (auto dest: in_set_dropD)
  have fp: "finite (gands_pos ps t (take (length ps) r))" by (rule finite_dands_pos[OF ft ftk])
  show ?thesis
    unfolding Cons Dense_Imp.dmulti_join_def gmulti_join_def
    by (sep_auto heap: dands_pos_h_rule[OF ft ftk] dands_neg_h_rule[OF fp fdr])
qed

text \<open>
  So the heap index computes what @{const gmulti_join} computes, whatever the flag
  @{const dense_heap_join} is set to and whichever side the length test picks -- which is what
  @{text \<open>-dense -heap_maps\<close>} needed and did not have.
\<close>

(*<*)
end
(*>*)
