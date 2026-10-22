(*<*)
theory Match_Window_Simulation
  imports "Monitor_Exec.Match_Window" Exec_Since_Simulation Exec_Until_Simulation "Monitor_Impl_Proof.Monitor_Instance_Valid"
begin
(*>*)

section \<open>The match structures over ascending columns\<close>

text \<open>
  The regular-expression nodes need no executable operations of their own.  Every table a match node
  handles lives over the node's own columns or over an atom's, and the reordering turns the
  kernel's operations into the very same operations over the ascending columns: the joins are
  @{thm [source] etabc_join_sub}, the unions are @{thm [source] etabc_Un_img}.  The one thing
  that does not come for free is that the guards really are tables over the node's columns: that
  is the regular expression's safety condition, and the lemmas below carry it.
\<close>

lemma wf_atomsD:
  assumes "wf_atoms ks kss css rels" "i < length rels"
  shows "eframe (kss ! i) (css ! i)" "set (kss ! i) \<subseteq> set ks" "table (kss ! i) (rels ! i)"
  using assms by (auto simp: wf_atoms_def)

subsection \<open>The lax epsilon\<close>

lemma table_eps_lax:
  assumes wf: "wf_atoms ks kss css rels"
  shows "ok (length rels) mr \<Longrightarrow> table ks guard \<Longrightarrow> table ks (\<epsilon>_lax ks kss guard rels mr)"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: table_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length rels" by simp
  show ?case by (simp, rule table_join_sub[OF MTestPos(2) wf_atomsD(3)[OF wf i] wf_atomsD(2)[OF wf i]])
next
  case (MTestNeg i)
  then have i: "i < length rels" by simp
  show ?case by (simp, rule table_join_sub[OF MTestNeg(2) wf_atomsD(3)[OF wf i] wf_atomsD(2)[OF wf i]])
next
  case (MPlus r t)
  then show ?case by simp
next
  case (MTimes r t)
  then show ?case by (auto intro: table_join_sub)
next
  case (MStar r)
  then show ?case by simp
qed

lemma etabc_eps_lax:
  assumes fK: "eframe ks cs" and wf: "wf_atoms ks kss css rels"
  shows "ok (length rels) mr \<Longrightarrow> table ks guard \<Longrightarrow>
     etabc ks cs (\<epsilon>_lax ks kss guard rels mr) = \<epsilon>_lax cs css (etabc ks cs guard) (etabcs kss css rels) mr"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length rels" by simp
  show ?case using i
    by (simp add: etabc_join_sub[OF fK wf_atomsD(1,2)[OF wf i] MTestPos(2) wf_atomsD(3)[OF wf i]])
next
  case (MTestNeg i)
  then have i: "i < length rels" by simp
  show ?case using i
    by (simp add: etabc_join_sub[OF fK wf_atomsD(1,2)[OF wf i] MTestNeg(2) wf_atomsD(3)[OF wf i]])
next
  case (MPlus r t)
  then show ?case by (simp add: etabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length rels) r" and o2: "ok (length rels) t" using MTimes(3) by simp_all
  have t1: "table ks (\<epsilon>_lax ks kss guard rels r)" by (rule table_eps_lax[OF wf o1 MTimes(4)])
  have t2: "table ks (\<epsilon>_lax ks kss guard rels t)" by (rule table_eps_lax[OF wf o2 MTimes(4)])
  show ?case using MTimes(1)[OF o1 MTimes(4)] MTimes(2)[OF o2 MTimes(4)]
    by (simp add: etabc_join_sub[OF fK fK subset_refl t1 t2])
qed simp

subsection \<open>The strict epsilons\<close>

text \<open>
  Unlike the lax one, a strict epsilon does not carry a guard, and its value is a table over the
  node's columns only because the regular expression is safe.  This is the column part of the
  kernel's @{thm [source] qtable_r\<epsilon>_strict} and @{thm [source] qtable_l\<epsilon>_strict}:
  restricted to no valuation at all, a @{const qtable} says only that its table is a finite table
  over its columns.
\<close>

lemma qtable_mem_restr_empty: "qtable cs (mem_restr {} cs) Q X \<longleftrightarrow> table cs X \<and> finite X"
  by (simp add: qtable_def mem_restr_def)

lemma table_reps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s)"
    and "ok (length \<psi>s) mr" and "set A = fv_regex (from_mregex mr \<psi>s)" "distinct A"
    and "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel \<and> finite rel) \<psi>s rels"
  shows "table A (r\<epsilon>_strict A (map Formula.fv_list \<psi>s) rels mr)"
  using qtable_r\<epsilon>_strict[OF assms(1-4), where R = "{}"] assms(5)
  by (simp add: qtable_mem_restr_empty)

lemma table_leps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s)"
    and "ok (length \<psi>s) mr" and "set A = fv_regex (from_mregex mr \<psi>s)" "distinct A"
    and "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel \<and> finite rel) \<psi>s rels"
  shows "table A (l\<epsilon>_strict A (map Formula.fv_list \<psi>s) rels mr)"
  using qtable_l\<epsilon>_strict[OF assms(1-4), where R = "{}"] assms(5)
  by (simp add: qtable_mem_restr_empty)

text \<open>A tested atom is moved to the node's column order; the executable one is already in it.\<close>

lemma etabc_reorder:
  assumes fK: "eframe ks cs" and f: "eframe k c" and e: "set k = set ks" and t: "table k T"
  shows "etabc ks cs (reorder ks k T) = reorder cs c (etabc k c T)"
proof -
  have cc: "c = cs"
    using eframeD(2,3)[OF fK] eframeD(2,3)[OF f] e by (intro strict_sorted_equal) auto
  have r: "reorder ks k T = restrict ks k ` T"
    using t restrict_idle[OF eframeD(1)[OF f]] by (force simp: reorder_def table_def)
  have fk: "eframe k cs" using f cc by simp
  show ?thesis
    unfolding r cc reorder_def using etabc_restrict[OF fk e[symmetric] t] by simp
qed

context eregex_frame begin

lemma wf_atoms: "wfrels rels \<Longrightarrow> wf_atoms ks (map Formula.fv_list \<psi>s) css rels"
  using lc fa sub by (auto simp: wf_atoms_def list_all2_conv_all_nth)

lemma etabc_reps_strict:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     etabc ks cs (r\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels mr)
       = r\<epsilon>_strict cs css (erels rels) mr"
proof (induct mr)
  case (MSkip m)
  then have "ks = []" by simp
  then have "cs = []" using eframeD(3)[OF fK] by simp
  with \<open>ks = []\<close> show ?case by (simp add: etabc_unit_table)
next
  case (MTestPos i)
  then have i: "i < length rels" using lr[OF ops] by simp
  have e: "set (Formula.fv_list (\<psi>s ! i)) = set ks" using MTestPos(3) by simp
  have t: "table (Formula.fv_list (\<psi>s ! i)) (rels ! i)" using ops i by (simp add: list_all2_conv_all_nth)
  show ?case using i lr[OF ops]
    by (simp add: etabc_reorder[OF fK fa e t])
next
  case (MTestNeg i)
  then have i: "i < length rels" using lr[OF ops] by simp
  have ek: "distinct ks" by (rule eframeD(1)[OF fK])
  have tb: "table ks (r\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels (MTestNeg i))"
    by (rule table_reps_strict[OF MTestNeg(1,2,3) ek ops])
  show ?case
  proof (cases "rels ! i = empty_table")
    case True
    then have "ks = []" using tb by (simp add: table_unit_table_Nil)
    then have "cs = []" using eframeD(3)[OF fK] by simp
    then show ?thesis using True i \<open>ks = []\<close> lr[OF ops] by (simp add: etabc_unit_table)
  next
    case False
    then show ?thesis using i lr[OF ops] by simp
  qed
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case
    using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4)
    by (simp add: etabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr1: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex r \<psi>s)"
    using MTimes(3) by simp
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)" using MTimes(3,5) by auto
  have tg: "table ks (r\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels r)"
    by (rule table_reps_strict[OF sr1 o1 fvr eframeD(1)[OF fK] ops])
  show ?case
    using MTimes(1)[OF sr1 o1 fvr] o2 lr[OF ops]
    by (simp add: etabc_eps_lax[OF fK wf_atoms[OF ops] _ tg])
next
  case (MStar r)
  have tb: "table ks (r\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels (MStar r))"
    by (rule table_reps_strict[OF MStar(2,3,4) eframeD(1)[OF fK] ops])
  then have "ks = []" by (simp add: table_unit_table_Nil)
  then have "cs = []" using eframeD(3)[OF fK] by simp
  with \<open>ks = []\<close> show ?case by (simp add: etabc_unit_table)
qed

lemma etabc_leps_strict:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     etabc ks cs (l\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels mr)
       = l\<epsilon>_strict cs css (erels rels) mr"
proof (induct mr)
  case (MSkip m)
  then have "ks = []" by simp
  then have "cs = []" using eframeD(3)[OF fK] by simp
  with \<open>ks = []\<close> show ?case by (simp add: etabc_unit_table)
next
  case (MTestPos i)
  then have i: "i < length rels" using lr[OF ops] by simp
  have e: "set (Formula.fv_list (\<psi>s ! i)) = set ks" using MTestPos(3) by simp
  have t: "table (Formula.fv_list (\<psi>s ! i)) (rels ! i)" using ops i by (simp add: list_all2_conv_all_nth)
  show ?case using i lr[OF ops]
    by (simp add: etabc_reorder[OF fK fa e t])
next
  case (MTestNeg i)
  then have i: "i < length rels" using lr[OF ops] by simp
  have tb: "table ks (l\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels (MTestNeg i))"
    by (rule table_leps_strict[OF MTestNeg(1,2,3) eframeD(1)[OF fK] ops])
  show ?case
  proof (cases "rels ! i = empty_table")
    case True
    then have "ks = []" using tb by (simp add: table_unit_table_Nil)
    then have "cs = []" using eframeD(3)[OF fK] by simp
    then show ?thesis using True i \<open>ks = []\<close> lr[OF ops] by (simp add: etabc_unit_table)
  next
    case False
    then show ?thesis using i lr[OF ops] by simp
  qed
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case
    using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4)
    by (simp add: etabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr2: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex t \<psi>s)"
    using MTimes(3) by simp
  have fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MTimes(3,5) by auto
  have tg: "table ks (l\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels t)"
    by (rule table_leps_strict[OF sr2 o2 fvt eframeD(1)[OF fK] ops])
  show ?case
    using MTimes(2)[OF sr2 o2 fvt] o1 lr[OF ops]
    by (simp add: etabc_eps_lax[OF fK wf_atoms[OF ops] _ tg])
next
  case (MStar r)
  have tb: "table ks (l\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels (MStar r))"
    by (rule table_leps_strict[OF MStar(2,3,4) eframeD(1)[OF fK] ops])
  then have "ks = []" by (simp add: table_unit_table_Nil)
  then have "cs = []" using eframeD(3)[OF fK] by simp
  with \<open>ks = []\<close> show ?case by (simp add: etabc_unit_table)
qed

end

subsection \<open>The derivatives\<close>

text \<open>
  The two derivatives read the previous firing's tabulation, which the node keeps reordered, and
  join what they find against the atoms through the lax epsilon.  Reordering a tabulation is
  reordering every entry, so the lookups agree; the rest is the lax epsilon again.
\<close>

lemma table_rdelta:
  assumes wf: "wf_atoms ks kss css rels" and X: "\<And>ms. table ks (lookup X ms)"
  shows "ok (length rels) mr \<Longrightarrow> table ks (r\<delta> ks kss \<kappa> X rels mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using X by (cases m) (auto simp: table_def empty_table_def)
next
  case (MPlus r t)
  then show ?case by simp
next
  case (MTimes r t)
  have o: "ok (length rels) r" "ok (length rels) t" using MTimes(3) by simp_all
  have u: "table ks (r\<delta> ks kss (\<lambda>u. \<kappa> (MTimes r u)) X rels t)" and g: "table ks (r\<delta> ks kss \<kappa> X rels r)"
    using MTimes(1,2) o by simp_all
  show ?case using u by (simp add: table_eps_lax[OF wf o(2) g])
qed (auto simp: table_def empty_table_def)

lemma table_ldelta:
  assumes wf: "wf_atoms ks kss css rels" and X: "\<And>ms. table ks (lookup X ms)"
  shows "ok (length rels) mr \<Longrightarrow> table ks (l\<delta> ks kss \<kappa> X rels mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using X by (cases m) (auto simp: table_def empty_table_def)
next
  case (MPlus r t)
  then show ?case by simp
next
  case (MTimes r t)
  have o: "ok (length rels) r" "ok (length rels) t" using MTimes(3) by simp_all
  have u: "table ks (l\<delta> ks kss (\<lambda>u. \<kappa> (MTimes u t)) X rels r)" and g: "table ks (l\<delta> ks kss \<kappa> X rels t)"
    using MTimes(1,2) o by simp_all
  show ?case using u by (simp add: table_eps_lax[OF wf o(1) g])
qed (auto simp: table_def empty_table_def)

lemma etabc_rdelta:
  assumes fK: "eframe ks cs" and wf: "wf_atoms ks kss css rels"
    and X: "\<And>ms. table ks (lookup X ms)" and dX: "\<And>ms. lookup dX ms = etabc ks cs (lookup X ms)"
  shows "ok (length rels) mr \<Longrightarrow>
     etabc ks cs (r\<delta> ks kss \<kappa> X rels mr) = r\<delta> cs css \<kappa> dX (etabcs kss css rels) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using dX by (cases m) (simp_all add: empty_table_def)
next
  case (MPlus r t)
  then show ?case by (simp add: etabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length rels) r" and o2: "ok (length rels) t" using MTimes(3) by simp_all
  have tg: "table ks (r\<delta> ks kss \<kappa> X rels r)" by (rule table_rdelta[OF wf X o1])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2]
    by (simp add: etabc_Un_img etabc_eps_lax[OF fK wf o2 tg])
qed (simp_all add: empty_table_def)

lemma etabc_ldelta:
  assumes fK: "eframe ks cs" and wf: "wf_atoms ks kss css rels"
    and X: "\<And>ms. table ks (lookup X ms)" and dX: "\<And>ms. lookup dX ms = etabc ks cs (lookup X ms)"
  shows "ok (length rels) mr \<Longrightarrow>
     etabc ks cs (l\<delta> ks kss \<kappa> X rels mr) = l\<delta> cs css \<kappa> dX (etabcs kss css rels) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using dX by (cases m) (simp_all add: empty_table_def)
next
  case (MPlus r t)
  then show ?case by (simp add: etabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length rels) r" and o2: "ok (length rels) t" using MTimes(3) by simp_all
  have tg: "table ks (l\<delta> ks kss \<kappa> X rels t)" by (rule table_ldelta[OF wf X o2])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2]
    by (simp add: etabc_Un_img etabc_eps_lax[OF fK wf o1 tg])
qed (simp_all add: empty_table_def)

lemma emrd_rel_length: "emrd_rel ks cs aux daux \<Longrightarrow> length aux = length daux"
  by (simp add: emrd_rel_def list_all2_lengthD)

lemma emrd_rel_induct[consumes 1, case_names Nil Cons]:
  assumes "emrd_rel ks cs aux daux"
    and "P [] []"
    and "\<And>t X X' aux daux. (\<forall>ms. table ks (lookup X ms)) \<Longrightarrow>
       (\<forall>ms. lookup X' ms = etabc ks cs (lookup X ms)) \<Longrightarrow> emrd_rel ks cs aux daux \<Longrightarrow>
       P aux daux \<Longrightarrow> P ((t, X) # aux) ((t, X') # daux)"
  shows "P aux daux"
  using assms(1)[unfolded emrd_rel_def]
  by (induct rule: list_all2_induct) (use assms(2,3) in \<open>auto simp: emrd_rel_def\<close>)

text \<open>Reordering a tabulation entry by entry is reordering what it tabulates.\<close>

lemma lookup_mrtabulate_cong:
  assumes d: "distinct mrs" and f: "\<And>ms. ms \<in> set mrs \<Longrightarrow> etabc ks cs (f ms) = g ms"
  shows "lookup (mrtabulate mrs g) ms = etabc ks cs (lookup (mrtabulate mrs f) ms)"
  using f by (simp add: lookup_tabulate[OF d] empty_table_def)

text \<open>Reading a structure is a union of lookups, which the reordering distributes over.\<close>

lemma etabc_foldr_lookup:
  assumes "emrd_rel ks cs aux daux"
  shows "etabc ks cs (foldr (\<union>) [lookup rel ms. (t, rel) \<leftarrow> aux, P t] {})
       = foldr (\<union>) [lookup rel ms. (t, rel) \<leftarrow> daux, P t] {}"
  using assms by (induct rule: emrd_rel_induct) (auto simp: etabc_Un_img etabc_def)

context ematchP_frame begin

lemma wfa: "wf_atoms ks kss css rels" by (rule wf_atoms[OF ops])

lemma tabT: "ms \<in> set mrs \<Longrightarrow> table ks (r\<epsilon>_strict ks kss rels ms)"
  using mrsok by (intro table_reps_strict[OF _ _ _ eframeD(1)[OF fK] ops]) auto

lemma etabT: "ms \<in> set mrs \<Longrightarrow> etabc ks cs (r\<epsilon>_strict ks kss rels ms) = r\<epsilon>_strict cs css (erels rels) ms"
  using mrsok by (intro etabc_reps_strict[OF ops]) auto

lemma table_lookup_head: "table ks (lookup (mrtabulate mrs (r\<epsilon>_strict ks kss rels)) ms)"
  using tabT by (simp add: lookup_tabulate[OF d])

lemma etabc_lookup_head:
  "lookup (mrtabulate mrs (r\<epsilon>_strict cs css (erels rels))) ms
     = etabc ks cs (lookup (mrtabulate mrs (r\<epsilon>_strict ks kss rels)) ms)"
  by (rule lookup_mrtabulate_cong[OF d etabT])

lemma emrd_rel_head:
  "emrd_rel ks cs [(nt, mrtabulate mrs (r\<epsilon>_strict ks kss rels))]
     [(nt, mrtabulate mrs (r\<epsilon>_strict cs css (erels rels)))]"
  using table_lookup_head etabc_lookup_head by simp

lemma emrd_rel_step:
  assumes rel: "emrd_rel ks cs aux daux"
  shows "emrd_rel ks cs
     [(t, mrtabulate mrs (\<lambda>ms. r\<delta> ks kss id X rels ms \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))).
        (t, X) \<leftarrow> aux, memR I (nt - t)]
     [(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
          \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))).
        (t, X) \<leftarrow> daux, memR I (nt - t)]"
  using rel
proof (induct rule: emrd_rel_induct)
  case (Cons t X X' aux daux)
  have okms: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ok (length rels) ms" using mrsok lr[OF ops] by auto
  have tX: "\<And>ms. table ks (lookup X ms)" using Cons(1) by blast
  have dXe: "\<And>ms. lookup X' ms = etabc ks cs (lookup X ms)" using Cons(2) by blast
  have tD: "\<And>ms. ms \<in> set mrs \<Longrightarrow> table ks (r\<delta> ks kss id X rels ms)"
    by (rule table_rdelta[OF wfa tX okms])
  have tE: "\<And>ms. table ks
      (lookup (mrtabulate mrs (\<lambda>ms. r\<delta> ks kss id X rels ms
         \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))) ms)"
    using tD tabT by (auto simp: lookup_tabulate[OF d] table_def empty_table_def)
  have dR: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      etabc ks cs (r\<delta> ks kss id X rels ms) = r\<delta> cs css id X' (erels rels) ms"
    by (rule etabc_rdelta[OF fK wfa tX dXe okms])
  have dD: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      etabc ks cs (r\<delta> ks kss id X rels ms \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))
        = r\<delta> cs css id X' (erels rels) ms
          \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {})"
    by (simp add: etabc_Un_img dR etabT)
  have dE: "\<And>ms. lookup (mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X' (erels rels) ms
         \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))) ms
      = etabc ks cs (lookup (mrtabulate mrs (\<lambda>ms. r\<delta> ks kss id X rels ms
         \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))) ms)"
    by (rule lookup_mrtabulate_cong[OF d dD])
  show ?case using Cons(4) tE dE by simp
qed simp

lemma etabc_update_matchP:
  assumes rel: "emrd_rel ks cs aux daux"
  shows "etabc ks cs (fst (update_matchP ks kss I mr mrs rels nt aux))
       = fst (update_matchP cs css I mr mrs (erels rels) nt daux) \<and>
     emrd_rel ks cs (snd (update_matchP ks kss I mr mrs rels nt aux))
       (snd (update_matchP cs css I mr mrs (erels rels) nt daux))"
proof -
  let ?W = "[(t, mrtabulate mrs (\<lambda>ms. r\<delta> ks kss id X rels ms
       \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))). (t, X) \<leftarrow> aux, memR I (nt - t)]"
  let ?D = "[(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))).
         (t, X) \<leftarrow> daux, memR I (nt - t)]"
  have st: "emrd_rel ks cs ?W ?D" by (rule emrd_rel_step[OF rel])
  have both: "emrd_rel ks cs
      (case ?W of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict ks kss rels))]
       | x # w' \<Rightarrow> (if fst x = nt then x # w'
                   else (nt, mrtabulate mrs (r\<epsilon>_strict ks kss rels)) # x # w'))
      (case ?D of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict cs css (erels rels)))]
       | x # w' \<Rightarrow> (if fst x = nt then x # w'
                   else (nt, mrtabulate mrs (r\<epsilon>_strict cs css (erels rels))) # x # w'))"
  proof (cases ?W)
    case Nil
    have DN: "?D = []" using emrd_rel_length[OF st] unfolding Nil by simp
    show ?thesis unfolding Nil DN using emrd_rel_head by simp
  next
    case (Cons x w')
    have "length ?D = Suc (length w')" using emrd_rel_length[OF st] unfolding Cons by simp
    then obtain y d' where D: "?D = y # d'" by (cases ?D) auto
    have rel': "emrd_rel ks cs (x # w') (y # d')" using st unfolding Cons D .
    show ?thesis unfolding Cons D
      using rel' table_lookup_head etabc_lookup_head
      by (cases x; cases y) auto
  qed
  show ?thesis
    using both etabc_foldr_lookup[OF both]
    by (simp add: update_matchP_def Let_def)
qed

end

lemma emld_rel_induct[consumes 1, case_names Nil Cons]:
  assumes "emld_rel ks cs \<psi>s css aux daux"
    and "P [] []"
    and "\<And>t rls rel aux daux. list_all2 (\<lambda>\<psi> r. table (Formula.fv_list \<psi>) r \<and> finite r) \<psi>s rls \<Longrightarrow>
       emld_rel ks cs \<psi>s css aux daux \<Longrightarrow> P aux daux \<Longrightarrow>
       P ((t, rls, rel) # aux) ((t, etabcs (map Formula.fv_list \<psi>s) css rls, etabc ks cs rel) # daux)"
  shows "P aux daux"
  using assms(1)[unfolded emld_rel_def]
  by (induct rule: list_all2_induct) (use assms(2,3) in \<open>auto simp: emld_rel_def\<close>)

context ematchF_frame begin

lemma okms: "ms \<in> set mrs \<Longrightarrow> wfrels rels \<Longrightarrow> ok (length rels) ms"
  using mrsok lr by auto

lemma tabL: "wfrels rels \<Longrightarrow> ms \<in> set mrs \<Longrightarrow> table ks (l\<epsilon>_strict ks kss rels ms)"
  using mrsok by (intro table_leps_strict[OF _ _ _ eframeD(1)[OF fK]]) auto

lemma etabL: "wfrels rels \<Longrightarrow> ms \<in> set mrs \<Longrightarrow>
    etabc ks cs (l\<epsilon>_strict ks kss rels ms) = l\<epsilon>_strict cs css (erels rels) ms"
  using mrsok by (intro etabc_leps_strict) auto

lemma table_lookup_base:
  "wfrels rels \<Longrightarrow> table ks (lookup (mrtabulate mrs (l\<epsilon>_strict ks kss rels)) ms)"
  using tabL by (simp add: lookup_tabulate[OF d])

lemma etabc_lookup_base:
  "wfrels rels \<Longrightarrow>
     lookup (mrtabulate mrs (l\<epsilon>_strict cs css (erels rels))) ms
       = etabc ks cs (lookup (mrtabulate mrs (l\<epsilon>_strict ks kss rels)) ms)"
  by (intro lookup_mrtabulate_cong[OF d]) (rule etabL)

lemma table_lookup_step:
  assumes rls: "wfrels rls" and X: "\<And>ms. table ks (lookup X ms)"
  shows "table ks (lookup (mrtabulate mrs (l\<delta> ks kss id X rls)) ms)"
  using table_ldelta[OF wf_atoms[OF rls] X] okms[OF _ rls]
  by (auto simp: lookup_tabulate[OF d] table_def empty_table_def)

lemma etabc_matchF_foldr:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "emld_rel ks cs \<psi>s css
       (fst (foldr (update_matchF_step ks kss I mr mrs nt) aux
          (update_matchF_base ks kss I mr mrs rels nt)))
       (fst (foldr (update_matchF_step cs css I mr mrs nt) daux
          (update_matchF_base cs css I mr mrs (erels rels) nt)))
     \<and> (\<forall>ms. table ks
          (lookup (snd (foldr (update_matchF_step ks kss I mr mrs nt) aux
             (update_matchF_base ks kss I mr mrs rels nt))) ms))
     \<and> (\<forall>ms. lookup (snd (foldr (update_matchF_step cs css I mr mrs nt) daux
             (update_matchF_base cs css I mr mrs (erels rels) nt))) ms
          = etabc ks cs (lookup (snd (foldr (update_matchF_step ks kss I mr mrs nt) aux
             (update_matchF_base ks kss I mr mrs rels nt))) ms))"
  using rel
proof (induct rule: emld_rel_induct)
  case Nil
  show ?case
    using rels table_lookup_base[OF rels] etabc_lookup_base[OF rels]
    by (simp add: update_matchF_base_def Let_def empty_table_def)
next
  case (Cons t rls rel aux daux)
  obtain A X where W: "foldr (update_matchF_step ks kss I mr mrs nt) aux
      (update_matchF_base ks kss I mr mrs rels nt) = (A, X)"
    by (cases "foldr (update_matchF_step ks kss I mr mrs nt) aux
      (update_matchF_base ks kss I mr mrs rels nt)")
  obtain DA DX where D: "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (erels rels) nt) = (DA, DX)"
    by (cases "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (erels rels) nt)")
  have IH: "emld_rel ks cs \<psi>s css A DA" and tX: "\<And>ms. table ks (lookup X ms)"
    and dXe: "\<And>ms. lookup DX ms = etabc ks cs (lookup X ms)"
    using Cons(3) unfolding W D by simp_all
  have tY: "\<forall>ms. table ks (lookup (mrtabulate mrs (l\<delta> ks kss id X rls)) ms)"
    using table_lookup_step[OF Cons(1) tX] by blast
  have dLY: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      etabc ks cs (l\<delta> ks kss id X rls ms) = l\<delta> cs css id DX (erels rls) ms"
    by (rule etabc_ldelta[OF fK wf_atoms[OF Cons(1)] tX dXe okms[OF _ Cons(1)]])
  have dY: "\<forall>ms. lookup (mrtabulate mrs (l\<delta> cs css id DX (erels rls))) ms
      = etabc ks cs (lookup (mrtabulate mrs (l\<delta> ks kss id X rls)) ms)"
    by (intro allI lookup_mrtabulate_cong[OF d, where f = "l\<delta> ks kss id X rls"
        and g = "l\<delta> cs css id DX (erels rls)"]) (rule dLY)
  have E: "foldr (update_matchF_step ks kss I mr mrs nt) ((t, rls, rel) # aux)
      (update_matchF_base ks kss I mr mrs rels nt)
      = update_matchF_step ks kss I mr mrs nt (t, rls, rel) (A, X)"
    unfolding W[symmetric] by simp
  have DE: "foldr (update_matchF_step cs css I mr mrs nt)
      ((t, erels rls, etabc ks cs rel) # daux)
      (update_matchF_base cs css I mr mrs (erels rels) nt)
      = update_matchF_step cs css I mr mrs nt (t, erels rls, etabc ks cs rel) (DA, DX)"
    unfolding D[symmetric] by simp
  show ?case unfolding E DE
    using IH tY dY Cons(1)
    by (simp add: update_matchF_step_def Let_def etabc_Un_img)
qed

lemma etabc_update_matchF:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "emld_rel ks cs \<psi>s css (update_matchF ks kss I mr mrs rels nt aux)
     (update_matchF cs css I mr mrs (erels rels) nt daux)"
  using etabc_matchF_foldr[OF rels rel] by (simp add: update_matchF_def)

text \<open>Reading the structure hands out the entries that have left the window, reordered.\<close>

lemma etabc_eval_matchF:
  assumes "emld_rel ks cs \<psi>s css aux daux"
  shows "fst (eval_matchF I mr nt daux) = map (etabc ks cs) (fst (eval_matchF I mr nt aux)) \<and>
     emld_rel ks cs \<psi>s css (snd (eval_matchF I mr nt aux)) (snd (eval_matchF I mr nt daux))"
  using assms
proof (induct rule: emld_rel_induct)
  case (Cons t rls rel aux daux)
  obtain ys ax where e: "eval_matchF I mr nt aux = (ys, ax)"
    by (cases "eval_matchF I mr nt aux")
  obtain dys dax where de: "eval_matchF I mr nt daux = (dys, dax)"
    by (cases "eval_matchF I mr nt daux")
  have i1: "dys = map (etabc ks cs) ys" and i2: "emld_rel ks cs \<psi>s css ax dax"
    using Cons(3) unfolding e de by simp_all
  show ?case using Cons(1,2) i1 i2 by (simp add: e de)
qed simp

end

section \<open>The match windows the executable evaluator runs\<close>

text \<open>
  The section above relates the kernel's match windows at the kernel's
  columns to the kernel's windows run at the ascending columns, on the reordered operands.  The
  windows below are what the executable evaluator runs:
  an operand is probed by the semi-join against its mask instead of the kernel's join, and they
  are polymorphic in the field type.  This theory shows that at the ascending columns they are
  the kernel's windows, so the relations @{const emrd_rel} and @{const emld_rel} of
  @{theory Monitor_Exec.Match_Window} hold of them unchanged.

  Two things differ from the kernel's derivatives.  The join against an atom is a semi-join,
  which @{thm [source] join_sub_eq} relates to the kernel's join; and the join of two lax
  epsilons is an intersection, which it is because both are tables over the node's columns.  The
  unit table is the empty tuple, which is the kernel's, and a strict epsilon's atom needs no
  reordering, because its columns are the node's.
\<close>

lemma mrg_left_key_map:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     mrg_left_key (mrg_plan cs1 cs2) = map (\<lambda>c. c \<in> set cs2) cs1"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: mrg_left_key_MRgt)
next
  case (2 c cs)
  then show ?case by simp
next
  case (3 c cs d ds)
  note cc = mrg_plan_Cons_cases[OF 3(4,5,6)]
  show ?case
  proof (cases "c < d")
    case True
    have "c \<notin> set (d # ds)" using True 3(5) by auto
    moreover have "c \<noteq> d" using True by simp
    ultimately show ?thesis using 3(1)[OF True] 3(4,5) cc(2)[OF True] by simp
  next
    case False
    then have e: "c = d" using cc(1) by simp
    have "map (\<lambda>x. x \<in> set (c # ds)) cs = map (\<lambda>x. x \<in> set ds) cs" using 3(4) by auto
    then show ?thesis using 3(3)[OF False cc(1)] 3(4,5) cc(3)[OF e] False e by simp
  qed
qed

lemma emb_msk_emb_plan:
  assumes s1: "sorted_wrt (<) cs" and s2: "sorted_wrt (<) c" and sub: "set c \<subseteq> set cs"
  shows "emb_msk (emb_plan cs c) = emsk cs c"
  by (simp add: emb_msk_def emb_plan_def emsk_def mrg_left_key_map[OF s1 s2 sub] comp_def)

lemma eproj_dmsk:
  assumes s1: "sorted_wrt (<) cs" and s2: "sorted_wrt (<) ds" and sub: "set ds \<subseteq> set cs"
    and l: "length a = length cs"
  shows "eproj (emsk cs ds) a = restrict ds cs a"
  using emsk_args_dproj[OF emsk_args_dargs[OF s1 s2 sub, of undefined], of a] l
  by (simp add: emsk_def)

text \<open>The window's lookup and tabulation are the kernel's.\<close>

lemma glookup_lookup: "glookup = lookup"
  by (simp add: glookup_def Monitor.lookup_def empty_table_def)

lemma gmrtabulate_mrtabulate: "gmrtabulate xs f = mrtabulate xs f"
  by transfer (simp add: empty_table_def)

lemma mrtabulate_cong:
  assumes "\<And>k. k \<in> set ks \<Longrightarrow> f k = g k"
  shows "mrtabulate ks f = mrtabulate ks g"
proof -
  have "List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) ks
      = List.map_filter (\<lambda>k. let fk = g k in if fk = empty_table then None else Some (k, fk)) ks"
    using assms
  proof (induct ks)
    case (Cons a ks)
    then have "f a = g a" by simp
    with Cons show ?case by (simp add: Let_def)
  qed simp
  then show ?thesis unfolding mrtabulate.abs_eq by simp
qed

subsection \<open>The lax epsilon\<close>

lemma join_same:
  assumes d: "distinct cs" and tA: "table cs A" and tB: "table cs B"
  shows "join cs A True cs B = A \<inter> B"
  using join_sub_eq[OF d d tA tB subset_refl, of True] tA
  by (auto simp: table_def restrict_idle[OF d])

lemma geps_lax_eq:
  assumes s: "sorted_wrt (<) cs" and wf: "wf_atoms cs css css \<phi>s"
  shows "ok (length \<phi>s) mr \<Longrightarrow> table cs guard \<Longrightarrow>
     geps_lax (map (emsk cs) css) guard \<phi>s mr = \<epsilon>_lax cs css guard \<phi>s mr"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<phi>s" by simp
  have lc: "length css = length \<phi>s" using wf by (simp add: wf_atoms_def)
  have fi: "eframe (css ! i) (css ! i)" and si: "set (css ! i) \<subseteq> set cs"
    and ti: "table (css ! i) (\<phi>s ! i)" using wf_atomsD[OF wf i] by simp_all
  have dc: "distinct cs" using s by (simp add: strict_sorted_iff)
  have p: "\<And>a. a \<in> guard \<Longrightarrow> eproj (emsk cs (css ! i)) a = restrict (css ! i) cs a"
    using MTestPos(2) eproj_dmsk[OF s eframeD(2)[OF fi] si] by (auto simp: table_def wf_tuple_def)
  show ?case using i lc join_sub_eq[OF dc eframeD(1)[OF fi] MTestPos(2) ti si, of True] p
    by (auto simp: esemi_def)
next
  case (MTestNeg i)
  then have i: "i < length \<phi>s" by simp
  have lc: "length css = length \<phi>s" using wf by (simp add: wf_atoms_def)
  have fi: "eframe (css ! i) (css ! i)" and si: "set (css ! i) \<subseteq> set cs"
    and ti: "table (css ! i) (\<phi>s ! i)" using wf_atomsD[OF wf i] by simp_all
  have dc: "distinct cs" using s by (simp add: strict_sorted_iff)
  have p: "\<And>a. a \<in> guard \<Longrightarrow> eproj (emsk cs (css ! i)) a = restrict (css ! i) cs a"
    using MTestNeg(2) eproj_dmsk[OF s eframeD(2)[OF fi] si] by (auto simp: table_def wf_tuple_def)
  show ?case using i lc join_sub_eq[OF dc eframeD(1)[OF fi] MTestNeg(2) ti si, of False] p
    by (auto simp: esemi_def)
next
  case (MPlus r t)
  then show ?case by simp
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have dc: "distinct cs" using s by (simp add: strict_sorted_iff)
  have t1: "table cs (\<epsilon>_lax cs css guard \<phi>s r)" by (rule table_eps_lax[OF wf o1 MTimes(4)])
  have t2: "table cs (\<epsilon>_lax cs css guard \<phi>s t)" by (rule table_eps_lax[OF wf o2 MTimes(4)])
  show ?case using MTimes(1)[OF o1 MTimes(4)] MTimes(2)[OF o2 MTimes(4)]
    by (simp add: join_same[OF dc t1 t2])
qed simp

lemma grdelta_eq:
  assumes s: "sorted_wrt (<) cs" and wf: "wf_atoms cs css css \<phi>s"
    and X: "\<And>ms. table cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> grdelta (map (emsk cs) css) \<kappa> X \<phi>s mr = r\<delta> cs css \<kappa> X \<phi>s mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case by (cases m) (simp_all add: glookup_lookup empty_table_def)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have tg: "table cs (r\<delta> cs css \<kappa> X \<phi>s r)" by (rule table_rdelta[OF wf X o1])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2] by (simp add: geps_lax_eq[OF s wf o2 tg])
qed (simp_all add: empty_table_def)

lemma gldelta_eq:
  assumes s: "sorted_wrt (<) cs" and wf: "wf_atoms cs css css \<phi>s"
    and X: "\<And>ms. table cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> gldelta (map (emsk cs) css) \<kappa> X \<phi>s mr = l\<delta> cs css \<kappa> X \<phi>s mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case by (cases m) (simp_all add: glookup_lookup empty_table_def)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have tg: "table cs (l\<delta> cs css \<kappa> X \<phi>s t)" by (rule table_ldelta[OF wf X o2])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2] by (simp add: geps_lax_eq[OF s wf o1 tg])
qed (simp_all add: empty_table_def)

context eregex_frame
begin

lemma ewf_atoms: "wfrels rels \<Longrightarrow> wf_atoms cs css css (erels rels)"
  using lc fa sub eframeD(3)[OF fK]
  by (auto simp: wf_atoms_def list_all2_conv_all_nth eframe_def table_etabc strict_sorted_iff)

lemma css_eq:
  assumes i: "i < length \<psi>s" and e: "Formula.fv (\<psi>s ! i) = set ks"
  shows "css ! i = cs"
  using eframeD(2,3)[OF fK] eframeD(2,3)[OF fa[OF i]] e by (intro strict_sorted_equal) auto

lemma greps_strict_eq:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     greps_strict gmsks (erels rels) mr = r\<epsilon>_strict cs css (erels rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (simp add: unit_table_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<psi>s" by simp
  have "css ! i = cs" using css_eq[OF i] MTestPos(3) by simp
  then show ?case using i lr[OF ops] by (simp add: reorder_def)
next
  case (MTestNeg i)
  then show ?case using lr[OF ops] by (simp add: unit_table_def empty_table_def)
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4) by simp
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr1: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex r \<psi>s)"
    using MTimes(3) by simp
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)" using MTimes(3,5) by auto
  have tg: "table cs (r\<epsilon>_strict cs css (erels rels) r)"
    using table_etabc etabc_reps_strict[OF ops sr1 o1 fvr] by metis
  show ?case using MTimes(1)[OF sr1 o1 fvr] o2 lr[OF ops]
    by (simp add: geps_lax_eq[OF eframeD(2)[OF fK] ewf_atoms[OF ops] _ tg])
next
  case (MStar r)
  then show ?case by (simp add: unit_table_def)
qed

lemma gleps_strict_eq:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     gleps_strict gmsks (erels rels) mr = l\<epsilon>_strict cs css (erels rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (simp add: unit_table_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<psi>s" by simp
  have "css ! i = cs" using css_eq[OF i] MTestPos(3) by simp
  then show ?case using i lr[OF ops] by (simp add: reorder_def)
next
  case (MTestNeg i)
  then show ?case using lr[OF ops] by (simp add: unit_table_def empty_table_def)
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4) by simp
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr2: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex t \<psi>s)"
    using MTimes(3) by simp
  have fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MTimes(3,5) by auto
  have tg: "table cs (l\<epsilon>_strict cs css (erels rels) t)"
    using table_etabc etabc_leps_strict[OF ops sr2 o2 fvt] by metis
  show ?case using MTimes(2)[OF sr2 o2 fvt] o1 lr[OF ops]
    by (simp add: geps_lax_eq[OF eframeD(2)[OF fK] ewf_atoms[OF ops] _ tg])
next
  case (MStar r)
  then show ?case by (simp add: unit_table_def)
qed

end

subsection \<open>The past-match window\<close>

lemma emrd_rel_table:
  "emrd_rel ks cs aux daux \<Longrightarrow> (t, X) \<in> set daux \<Longrightarrow> table cs (lookup X ms)"
  by (induct rule: emrd_rel_induct) (auto simp: table_etabc)

context ematchP_frame
begin

lemma ldrels: "length (erels rels) = length \<psi>s"
  using lr[OF ops] by simp

lemma gtab_head:
  "mrtabulate mrs (greps_strict gmsks (erels rels)) = mrtabulate mrs (r\<epsilon>_strict cs css (erels rels))"
  using mrsok by (intro mrtabulate_cong greps_strict_eq[OF ops]) auto

lemma gtab_step:
  assumes X: "\<And>ms. table cs (lookup X ms)"
  shows "mrtabulate mrs (\<lambda>ms. grdelta gmsks id X (erels rels) ms
       \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {}))
     = mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))"
proof (rule mrtabulate_cong)
  fix ms
  assume ms: "ms \<in> set mrs"
  have o: "ok (length (erels rels)) ms" using mrsok[OF ms] ldrels by simp
  show "grdelta gmsks id X (erels rels) ms \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {})
      = r\<delta> cs css id X (erels rels) ms \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {})"
    using mrsok[OF ms]
    by (simp add: grdelta_eq[OF eframeD(2)[OF fK] ewf_atoms[OF ops] X o] greps_strict_eq[OF ops])
qed

lemma gtab_window:
  "(\<And>t X ms. (t, X) \<in> set D \<Longrightarrow> table cs (lookup X ms)) \<Longrightarrow>
   [(t, mrtabulate mrs (\<lambda>ms. grdelta gmsks id X (erels rels) ms
       \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {}))). (t, X) \<leftarrow> D, memR I (nt - t)]
   = [(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))). (t, X) \<leftarrow> D, memR I (nt - t)]"
proof (induct D)
  case (Cons x D)
  obtain t X where x: "x = (t, X)" by (cases x)
  have "\<And>ms. table cs (lookup X ms)" using Cons(2)[of t X] x by simp
  moreover have "\<And>t X ms. (t, X) \<in> set D \<Longrightarrow> table cs (lookup X ms)"
    using Cons(2) by (metis list.set_intros(2))
  ultimately show ?case using Cons(1) x by (simp add: gtab_step)
qed simp

lemma gupdate_matchP_eq:
  assumes rel: "emrd_rel ks cs aux daux"
  shows "gupdate_matchP gmsks I mr mrs (erels rels) nt daux
     = update_matchP cs css I mr mrs (erels rels) nt daux"
proof -
  have w: "[(t, mrtabulate mrs (\<lambda>ms. grdelta gmsks id X (erels rels) ms
       \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {}))). (t, X) \<leftarrow> daux, memR I (nt - t)]
   = [(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))). (t, X) \<leftarrow> daux, memR I (nt - t)]"
    by (rule gtab_window[OF emrd_rel_table[OF rel]])
  show ?thesis
    unfolding gupdate_matchP_def update_matchP_def glookup_lookup gmrtabulate_mrtabulate gtab_head w ..
qed

lemma etabc_gupdate_matchP:
  assumes rel: "emrd_rel ks cs aux daux"
  shows "etabc ks cs (fst (update_matchP ks kss I mr mrs rels nt aux))
       = fst (gupdate_matchP gmsks I mr mrs (erels rels) nt daux) \<and>
     emrd_rel ks cs (snd (update_matchP ks kss I mr mrs rels nt aux))
       (snd (gupdate_matchP gmsks I mr mrs (erels rels) nt daux))"
  unfolding gupdate_matchP_eq[OF rel] by (rule etabc_update_matchP[OF rel])

end

subsection \<open>The future-match window\<close>

lemma geval_matchF_eval_matchF: "geval_matchF I mr nt aux = eval_matchF I mr nt aux"
  by (induct aux rule: eval_matchF.induct) simp_all

context ematchF_frame
begin

lemma table_lookup_dbase:
  assumes rels: "wfrels rels"
  shows "table cs (lookup (mrtabulate mrs (l\<epsilon>_strict cs css (erels rels))) ms)"
  using etabL[OF rels] by (simp add: lookup_tabulate[OF d] table_etabc flip: etabL[OF rels])

lemma gupdate_matchF_base_eq:
  assumes rels: "wfrels rels"
  shows "gupdate_matchF_base gmsks I mr mrs (erels rels) nt
     = update_matchF_base cs css I mr mrs (erels rels) nt"
proof -
  have "mrtabulate mrs (gleps_strict gmsks (erels rels)) = mrtabulate mrs (l\<epsilon>_strict cs css (erels rels))"
    using mrsok by (intro mrtabulate_cong gleps_strict_eq[OF rels]) auto
  then show ?thesis
    by (simp add: gupdate_matchF_base_def update_matchF_base_def glookup_lookup gmrtabulate_mrtabulate
        Let_def empty_table_def)
qed

lemma gupdate_matchF_step_eq:
  assumes rls: "wfrels rls" and X: "\<And>ms. table cs (lookup X ms)"
  shows "gupdate_matchF_step gmsks I mr mrs nt (t, erels rls, drel) (A, X)
       = update_matchF_step cs css I mr mrs nt (t, erels rls, drel) (A, X)"
    and "table cs (lookup (mrtabulate mrs (l\<delta> cs css id X (erels rls))) ms)"
proof -
  have o: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ok (length (erels rls)) ms" using okms[OF _ rls] by simp
  have "mrtabulate mrs (gldelta gmsks id X (erels rls)) = mrtabulate mrs (l\<delta> cs css id X (erels rls))"
    by (intro mrtabulate_cong gldelta_eq[OF eframeD(2)[OF fK] ewf_atoms[OF rls] X o])
  then show "gupdate_matchF_step gmsks I mr mrs nt (t, erels rls, drel) (A, X)
       = update_matchF_step cs css I mr mrs nt (t, erels rls, drel) (A, X)"
    by (simp add: gupdate_matchF_step_def update_matchF_step_def glookup_lookup gmrtabulate_mrtabulate
        Let_def)
  show "table cs (lookup (mrtabulate mrs (l\<delta> cs css id X (erels rls))) ms)"
    using table_ldelta[OF ewf_atoms[OF rls] X o]
    by (simp add: lookup_tabulate[OF d])
qed

lemma gmatchF_foldr_eq:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "foldr (gupdate_matchF_step gmsks I mr mrs nt) daux (gupdate_matchF_base gmsks I mr mrs (erels rels) nt)
       = foldr (update_matchF_step cs css I mr mrs nt) daux (update_matchF_base cs css I mr mrs (erels rels) nt)
     \<and> (\<forall>ms. table cs (lookup (snd (foldr (update_matchF_step cs css I mr mrs nt) daux
          (update_matchF_base cs css I mr mrs (erels rels) nt))) ms))"
  using rel
proof (induct rule: emld_rel_induct)
  case Nil
  show ?case using table_lookup_dbase[OF rels]
    by (simp add: gupdate_matchF_base_eq[OF rels] update_matchF_base_def Let_def)
next
  case (Cons t rls rel aux daux)
  obtain A X where W: "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (erels rels) nt) = (A, X)"
    by (cases "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (erels rels) nt)")
  have IH: "foldr (gupdate_matchF_step gmsks I mr mrs nt) daux
      (gupdate_matchF_base gmsks I mr mrs (erels rels) nt) = (A, X)"
    and tX: "\<And>ms. table cs (lookup X ms)" using Cons(3) unfolding W by simp_all
  have E: "foldr (update_matchF_step cs css I mr mrs nt) ((t, erels rls, etabc ks cs rel) # daux)
      (update_matchF_base cs css I mr mrs (erels rels) nt)
      = update_matchF_step cs css I mr mrs nt (t, erels rls, etabc ks cs rel) (A, X)"
    unfolding W[symmetric] by simp
  have GE: "foldr (gupdate_matchF_step gmsks I mr mrs nt) ((t, erels rls, etabc ks cs rel) # daux)
      (gupdate_matchF_base gmsks I mr mrs (erels rels) nt)
      = gupdate_matchF_step gmsks I mr mrs nt (t, erels rls, etabc ks cs rel) (A, X)"
    unfolding IH[symmetric] by simp
  show ?case unfolding E GE gupdate_matchF_step_eq(1)[OF Cons(1) tX]
    using gupdate_matchF_step_eq(2)[OF Cons(1) tX]
    by (simp add: update_matchF_step_def Let_def)
qed

lemma gupdate_matchF_eq:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "gupdate_matchF gmsks I mr mrs (erels rels) nt daux
     = update_matchF cs css I mr mrs (erels rels) nt daux"
  using gmatchF_foldr_eq[OF rels rel] by (simp add: gupdate_matchF_def update_matchF_def)

lemma etabc_gupdate_matchF:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "emld_rel ks cs \<psi>s css (update_matchF ks kss I mr mrs rels nt aux)
     (gupdate_matchF gmsks I mr mrs (erels rels) nt daux)"
  unfolding gupdate_matchF_eq[OF rels rel] by (rule etabc_update_matchF[OF rels rel])

lemma etabc_geval_matchF:
  assumes "emld_rel ks cs \<psi>s css aux daux"
  shows "fst (geval_matchF I mr nt daux) = map (etabc ks cs) (fst (eval_matchF I mr nt aux)) \<and>
     emld_rel ks cs \<psi>s css (snd (eval_matchF I mr nt aux)) (snd (geval_matchF I mr nt daux))"
  unfolding geval_matchF_eval_matchF by (rule etabc_eval_matchF[OF assms])

end

(*<*)
end
(*>*)
