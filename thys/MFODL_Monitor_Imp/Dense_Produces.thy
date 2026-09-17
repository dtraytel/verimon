(*<*)
theory Dense_Produces
  imports Dense_Eval "MFODL_Monitor_Devel.Correctness"
begin
(*>*)

section \<open>Discharging @{const produces}\<close>

text \<open>
  @{const produces} is the one thing the simulation assumes about the kernel's evaluation, and it
  is discharged node by node: for every constructor of the kernel's formula, a lemma saying that
  if the operands produce finite tables over their columns then so does the node.  Each such
  lemma is a coinduction of its own, with an invariant that says only what that node needs, so the
  whole discharge is modular rather than one monolithic invariant over the kernel's language.
\<close>

subsection \<open>The coinduction, packaged\<close>

lemma ftable_empty_table[simp]: "ftable n A empty_table"
  by (simp add: empty_table_def table_def)



text \<open>@{thm [source] produces.coinduct} with the trivial equations of its conclusion already
  solved, so that each node's lemma only has to name its own invariant.\<close>

lemma producesI[case_names init step]:
  assumes init: "X n A \<phi>"
    and step: "\<And>m B \<psi> j ts db xs \<psi>'. X m B \<psi> \<Longrightarrow> wf_db db \<Longrightarrow>
        meval j m ts db \<psi> = (xs, \<psi>') \<Longrightarrow>
        list_all (ftable m B) xs \<and> (X m B \<psi>' \<or> produces m B \<psi>')"
  shows "produces n A \<phi>"
  using init
proof (rule produces.coinduct)
  fix m B \<psi>
  assume X: "X m B \<psi>"
  have "\<forall>j ts db xs \<chi>. wf_db db \<longrightarrow> meval j m ts db \<psi> = (xs, \<chi>) \<longrightarrow>
      list_all (ftable m B) xs \<and> (X m B \<chi> \<or> produces m B \<chi>)"
    using step[OF X] by blast
  then show "\<exists>m' \<psi>' B'. m = m' \<and> B = B' \<and> \<psi> = \<psi>' \<and>
      (\<forall>j ts db xs \<chi>. wf_db db \<longrightarrow> meval j m' ts db \<psi>' = (xs, \<chi>) \<longrightarrow>
         list_all (ftable m' B') xs \<and> (X m' B' \<chi> \<or> produces m' B' \<chi>))"
    by blast
qed

text \<open>A node that does not change under evaluation.\<close>

lemma produces_fix:
  assumes "\<And>j ts db xs \<phi>'. wf_db db \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
      list_all (ftable n A) xs \<and> \<phi>' = \<phi>"
  shows "produces n A \<phi>"
  by (rule producesI[where X = "\<lambda>m B \<psi>. m = n \<and> B = A \<and> \<psi> = \<phi>"]) (use assms in auto)

text \<open>
  A node with one operand whose output is the operand's, mapped pointwise.  This covers every
  unary node of the kernel's language, and the table-and-finiteness obligation is the only thing
  that changes from one to the next.
\<close>

lemma produces_unop:
  assumes step: "\<And>j ts db \<psi> ys \<psi>'. meval j m ts db \<psi> = (ys, \<psi>') \<Longrightarrow>
      meval j n ts db (C \<psi>) = (map g ys, C \<psi>')"
    and tab: "\<And>Y. table m B Y \<Longrightarrow> finite Y \<Longrightarrow> table n A (g Y) \<and> finite (g Y)"
    and p: "produces m B \<phi>"
  shows "produces n A (C \<phi>)"
proof (rule producesI[where
    X = "\<lambda>n' A' \<psi>. n' = n \<and> A' = A \<and> (\<exists>\<chi>. \<psi> = C \<chi> \<and> produces m B \<chi>)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi>. C \<phi> = C \<chi> \<and> produces m B \<chi>)" using p by blast
next
  fix n' A' \<psi> j ts db xs \<psi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi>. \<psi> = C \<chi> \<and> produces m B \<chi>)"
    and w: "wf_db db" and e: "meval j n' ts db \<psi> = (xs, \<psi>')"
  from X obtain \<chi> where pc: "produces m B \<chi>" and psi: "\<psi> = C \<chi>" by blast
  obtain ys \<chi>' where e': "meval j m ts db \<chi> = (ys, \<chi>')" by (cases "meval j m ts db \<chi>")
  have "meval j n ts db (C \<chi>) = (map g ys, C \<chi>')" by (rule step[OF e'])
  then have x: "xs = map g ys" and f: "\<psi>' = C \<chi>'" using e X psi by simp_all
  have t: "list_all (ftable m B) ys" by (rule produces_tables[OF pc w e'])
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi>. \<psi>' = C \<chi> \<and> produces m B \<chi>)) \<or> produces n' A' \<psi>')"
    using X t produces_next[OF pc w e'] tab by (auto simp: x f list_all_iff)
qed

subsection \<open>Nodes whose output does not depend on the operand's tables\<close>

lemma produces_MRel: "table n A rel \<Longrightarrow> finite rel \<Longrightarrow> produces n A (mformula.MRel rel)"
proof (coinduction arbitrary: rel)
  case produces
  then show ?case by (auto simp: list_all_iff)
qed

lemma produces_MNeg: "produces n {} (mformula.MNeg \<phi>)"
proof (coinduction arbitrary: \<phi>)
  case produces
  then show ?case
    by (auto simp: list_all_iff unit_table_def empty_table_def table_def wf_tuple_def
        split: prod.splits)
qed


subsection \<open>The unary nodes\<close>

lemma produces_MAndRel:
  "produces n A \<phi> \<Longrightarrow> produces n A (mformula.MAndRel \<phi> conf)"
  by (rule produces_unop[where m = n and B = A and C = "\<lambda>\<psi>. mformula.MAndRel \<psi> conf"
      and g = "Set.filter (eval_constraint conf)"])
    (auto simp: table_def split: prod.splits)

lemma table_eval_assignment:
  "table n B Y \<Longrightarrow> fst conf < n \<Longrightarrow>
     table n (Set.insert (fst conf) B) (eval_assignment conf ` Y)"
  by (cases conf) (auto simp: table_def wf_tuple_def nth_list_update)

lemma produces_MAndAssign:
  assumes x: "fst conf < n" and p: "produces n B \<phi>"
  shows "produces n (Set.insert (fst conf) B) (mformula.MAndAssign \<phi> conf)"
  by (rule produces_unop[where m = n and B = B and C = "\<lambda>\<psi>. mformula.MAndAssign \<psi> conf"
      and g = "\<lambda>Y. eval_assignment conf ` Y", OF _ _ p])
    (use x in \<open>auto simp: table_eval_assignment split: prod.splits\<close>)

lemma produces_MExists:
  "produces (Suc n) B \<phi> \<Longrightarrow>
     produces n ((\<lambda>x. x - Suc 0) ` (B - {0})) (mformula.MExists \<phi>)"
  by (rule produces_unop[where m = "Suc n" and B = B and C = mformula.MExists
      and g = "\<lambda>Y. tl ` Y"])
    (auto simp: table_project split: prod.splits)


subsection \<open>The predicate and time nodes\<close>

lemma produces_MPred_Copy:
  assumes l: "length tms = n"
  shows "produces n {0..<n} (mformula.MPred e tms Copy)"
proof (rule produces_fix)
  fix j ts db xs \<phi>'
  assume w: "wf_db db" and m: "meval j n ts db (mformula.MPred e tms Copy) = (xs, \<phi>')"
  show "list_all (ftable n {0..<n}) xs \<and> \<phi>' = mformula.MPred e tms Copy"
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    then show ?thesis using m by (auto simp: list_all_iff table_def)
  next
    case (Some X)
    then show ?thesis using m w l
      by (auto simp: list_all_iff dest: wf_dbD wf_dbD_finite)
  qed
qed

lemma produces_MPred_Simple:
  assumes sp: "is_simple_pattern tms 0"
    and b: "\<forall>t \<in> set tms. \<forall>x \<in> Formula.fv_trm t. x < n"
  shows "produces n (\<Union>t \<in> set tms. Formula.fv_trm t) (mformula.MPred e tms Simple)"
proof (rule produces_fix)
  fix j ts db xs \<phi>'
  assume w: "wf_db db" and m: "meval j n ts db (mformula.MPred e tms Simple) = (xs, \<phi>')"
  show "list_all (ftable n (\<Union>t \<in> set tms. Formula.fv_trm t)) xs \<and>
      \<phi>' = mformula.MPred e tms Simple"
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    then show ?thesis using m by (auto simp: list_all_iff table_def)
  next
    case (Some X)
    have "\<And>T. T \<in> set X \<Longrightarrow>
        ftable n (\<Union>t \<in> set tms. Formula.fv_trm t) (simple_match n 0 tms ` T)"
    proof -
      fix T assume T: "T \<in> set X"
      have t: "table (length tms) {0..<length tms} T" by (rule wf_dbD[OF w Some T])
      have "\<And>y. y \<in> T \<Longrightarrow> wf_tuple n (\<Union>t \<in> set tms. Formula.fv_trm t) (simple_match n 0 tms y)"
        using t by (intro wf_tuple_simple_match[OF sp b])
          (auto simp: table_def wf_tuple_def in_set_conv_nth)
      then show "ftable n (\<Union>t \<in> set tms. Formula.fv_trm t) (simple_match n 0 tms ` T)"
        using wf_dbD_finite[OF w Some T] by (auto simp: table_def)
    qed
    then show ?thesis using m Some by (auto simp: list_all_iff)
  qed
qed

lemma produces_MPred_Match:
  "produces n (\<Union>t \<in> set tms. Formula.fv_trm t) (mformula.MPred e tms Match)"
proof (rule produces_fix)
  fix j ts db xs \<phi>'
  assume w: "wf_db db" and m: "meval j n ts db (mformula.MPred e tms Match) = (xs, \<phi>')"
  show "list_all (ftable n (\<Union>t \<in> set tms. Formula.fv_trm t)) xs \<and>
      \<phi>' = mformula.MPred e tms Match"
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    then show ?thesis using m by (auto simp: list_all_iff table_def)
  next
    case (Some X)
    have "\<And>T. T \<in> set X \<Longrightarrow> ftable n (\<Union>t \<in> set tms. Formula.fv_trm t)
        ((\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` T))"
    proof -
      fix T assume T: "T \<in> set X"
      have f: "finite T" by (rule wf_dbD_finite[OF w Some T])
      then have "finite (Option.these (match tms ` T))" by (simp add: finite_these)
      then show "ftable n (\<Union>t \<in> set tms. Formula.fv_trm t)
          ((\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` T))"
        by (auto simp: table_def in_these_eq intro: match_wf_tuple)
    qed
    then show ?thesis using m Some by (auto simp: list_all_iff)
  qed
qed

fun mtrm_cols :: "mtrm \<Rightarrow> nat set" where
  "mtrm_cols (MVar v) = {v}"
| "mtrm_cols (MConst c) = {}"

lemma ftable_eval_mtrm: "ftable n (mtrm_cols mt) (eval_mtrm n mt x)"
proof (cases mt)
  case (MVar v)
  have "table n {v} (singleton_table n v x)" by simp
  moreover have "finite (singleton_table n v x)" by (simp add: singleton_table_def)
  ultimately show ?thesis using MVar by simp
next
  case (MConst c)
  have "table n {} (unit_table n)" by simp
  moreover have "finite (unit_table n)" unfolding unit_table_def by simp
  ultimately show ?thesis using MConst by (auto simp: empty_table_def)
qed

lemma produces_MTP: "produces n (mtrm_cols mt) (mformula.MTP mt i)"
  by (rule producesI[where
      X = "\<lambda>m B \<psi>. m = n \<and> B = mtrm_cols mt \<and> (\<exists>k. \<psi> = mformula.MTP mt k)"])
    (auto simp: list_all_iff ftable_eval_mtrm)

lemma produces_MTS: "produces n (mtrm_cols mt) (mformula.MTS mt)"
  by (rule produces_fix) (auto simp: list_all_iff ftable_eval_mtrm)


subsection \<open>The binary nodes with a buffer\<close>

lemma mbuf2_take_out:
  "mbuf2_take f (xs, ys) = (zs, buf') \<Longrightarrow>
     (\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set ys \<Longrightarrow> P (f a b)) \<Longrightarrow> list_all P zs"
proof (induct xs arbitrary: ys zs buf')
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  note IH = Cons(1) and e = Cons(2) and st = Cons(3)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using e by simp
  next
    case (Cons y ys0)
    obtain ws bf where w: "mbuf2_take f (xs, ys0) = (ws, bf)"
      by (cases "mbuf2_take f (xs, ys0)")
    have z: "zs = f x y # ws" using e Cons w by simp
    have "list_all P ws" by (rule IH[OF w]) (use st Cons in simp)
    then show ?thesis using st Cons by (simp add: z)
  qed
qed

lemma produces_binop:
  assumes step: "\<And>j ts db \<chi> \<eta> bf as \<chi>' bs \<eta>' zs bf'.
      meval j n ts db \<chi> = (as, \<chi>') \<Longrightarrow> meval j n ts db \<eta> = (bs, \<eta>') \<Longrightarrow>
      mbuf2_take f (mbuf2_add as bs bf) = (zs, bf') \<Longrightarrow>
      meval j n ts db (C \<chi> \<eta> bf) = (zs, C \<chi>' \<eta>' bf')"
    and tab: "\<And>X Y. ftable n B1 X \<Longrightarrow> ftable n B2 Y \<Longrightarrow> ftable n A (f X Y)"
    and p1: "produces n B1 \<phi>" and p2: "produces n B2 \<psi>"
    and bf1: "list_all (ftable n B1) (fst buf)" and bf2: "list_all (ftable n B2) (snd buf)"
  shows "produces n A (C \<phi> \<psi> buf)"
proof (rule producesI[where X = "\<lambda>n' A' \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> \<eta> bf. \<Phi> = C \<chi> \<eta> bf \<and> produces n B1 \<chi> \<and> produces n B2 \<eta> \<and>
       list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> \<eta> bf. C \<phi> \<psi> buf = C \<chi> \<eta> bf \<and> produces n B1 \<chi> \<and>
      produces n B2 \<eta> \<and> list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))"
    using p1 p2 bf1 bf2 by blast
next
  fix n' A' \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi> \<eta> bf. \<Phi> = C \<chi> \<eta> bf \<and> produces n B1 \<chi> \<and>
      produces n B2 \<eta> \<and> list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))"
    and w: "wf_db db" and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> bf where Phi: "\<Phi> = C \<chi> \<eta> bf" and pc: "produces n B1 \<chi>"
    and pe: "produces n B2 \<eta>" and b1: "list_all (ftable n B1) (fst bf)"
    and b2: "list_all (ftable n B2) (snd bf)" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain zs c1 c2 where e3: "mbuf2_take f (mbuf2_add as bs bf) = (zs, (c1, c2))"
    by (cases "mbuf2_take f (mbuf2_add as bs bf)") auto
  have "meval j n ts db (C \<chi> \<eta> bf) = (zs, C \<chi>' \<eta>' (c1, c2))" by (rule step[OF e1 e2 e3])
  then have x: "xs = zs" and f': "\<Phi>' = C \<chi>' \<eta>' (c1, c2)" using e X Phi by simp_all
  have ta: "list_all (ftable n B1) as" by (rule produces_tables[OF pc w e1])
  have tb: "list_all (ftable n B2) bs" by (rule produces_tables[OF pe w e2])
  have add: "mbuf2_add as bs bf = (fst bf @ as, snd bf @ bs)" by (cases bf) simp
  have la: "list_all (ftable n B1) (fst bf @ as)" using b1 ta by simp
  have lb: "list_all (ftable n B2) (snd bf @ bs)" using b2 tb by simp
  have e3': "mbuf2_take f (fst bf @ as, snd bf @ bs) = (zs, (c1, c2))"
    using e3 unfolding add by simp
  have tz: "list_all (ftable n A) zs"
    by (rule mbuf2_take_out[OF e3']) (use la lb tab in \<open>auto simp: list_all_iff\<close>)
  have sb: "set c1 \<subseteq> set (fst bf @ as) \<and> set c2 \<subseteq> set (snd bf @ bs)"
    by (rule mbuf2_take_sub[OF e3'])
  have lc1: "list_all (ftable n B1) c1" using sb la by (auto simp: list_all_iff)
  have lc2: "list_all (ftable n B2) c2" using sb lb by (auto simp: list_all_iff)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> \<eta> bf. \<Phi>' = C \<chi> \<eta> bf \<and> produces n B1 \<chi> \<and> produces n B2 \<eta> \<and>
         list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))) \<or>
       produces n' A' \<Phi>')"
    using X tz lc1 lc2 produces_next[OF pc w e1] produces_next[OF pe w e2]
    by (auto simp: x f')
qed

lemma produces_MOr:
  assumes p1: "produces n A \<phi>" and p2: "produces n A \<psi>"
    and bf1: "list_all (ftable n A) (fst buf)" and bf2: "list_all (ftable n A) (snd buf)"
  shows "produces n A (mformula.MOr \<phi> \<psi> buf)"
proof -
  have step: "\<And>j ts db \<chi> \<eta> bf as \<chi>' bs \<eta>' zs bf'.
      meval j n ts db \<chi> = (as, \<chi>') \<Longrightarrow> meval j n ts db \<eta> = (bs, \<eta>') \<Longrightarrow>
      mbuf2_take (\<lambda>X Y. X \<union> Y) (mbuf2_add as bs bf) = (zs, bf') \<Longrightarrow>
      meval j n ts db (mformula.MOr \<chi> \<eta> bf) = (zs, mformula.MOr \<chi>' \<eta>' bf')"
    by simp
  have tab: "\<And>X Y. ftable n A X \<Longrightarrow> ftable n A Y \<Longrightarrow> ftable n A (X \<union> Y)"
    by (auto simp: table_def)
  show ?thesis by (rule produces_binop[OF step tab p1 p2 bf1 bf2])
qed

lemma ftable_bin_join:
  fixes X Y :: "event_data table"
  assumes tX: "ftable n A1 X" and tY: "ftable n A2 Y"
    and sub: "\<not> pos \<Longrightarrow> A2 \<subseteq> A1" and A: "A = (if pos then A1 \<union> A2 else A1)"
  shows "ftable n A (bin_join n A1 X pos A2 Y)"
proof -
  have tj: "table n A (join X pos Y)"
    by (rule join_table[of n A1 X A2 Y pos A]) (use tX tY sub A in auto)
  have fj: "finite (join X pos Y)" by (rule finite_join) (use tX tY in auto)
  have bj: "bin_join n A1 X pos A2 Y = join X pos Y"
    by (rule bin_join_table) (use tX tY in auto)
  show ?thesis unfolding bj using tj fj by simp
qed

lemma produces_MAnd:
  assumes p1: "produces n A1 \<phi>" and p2: "produces n A2 \<psi>"
    and bf1: "list_all (ftable n A1) (fst buf)" and bf2: "list_all (ftable n A2) (snd buf)"
    and sub: "\<not> pos \<Longrightarrow> A2 \<subseteq> A1" and A: "A = (if pos then A1 \<union> A2 else A1)"
  shows "produces n A (mformula.MAnd A1 \<phi> pos A2 \<psi> buf)"
proof -
  have step: "\<And>j ts db \<chi> \<eta> bf as \<chi>' bs \<eta>' zs bf'.
      meval j n ts db \<chi> = (as, \<chi>') \<Longrightarrow> meval j n ts db \<eta> = (bs, \<eta>') \<Longrightarrow>
      mbuf2_take (\<lambda>X Y. bin_join n A1 X pos A2 Y) (mbuf2_add as bs bf) = (zs, bf') \<Longrightarrow>
      meval j n ts db (mformula.MAnd A1 \<chi> pos A2 \<eta> bf)
        = (zs, mformula.MAnd A1 \<chi>' pos A2 \<eta>' bf')"
    by (simp del: bin_join.simps)
  show ?thesis
    by (rule produces_binop[OF step ftable_bin_join[OF _ _ sub A] p1 p2 bf1 bf2])
qed

subsection \<open>The temporal shift nodes\<close>

lemma mprev_next_out:
  "mprev_next I xs ts = (zs, xs', ts') \<Longrightarrow> list_all P xs \<Longrightarrow> P empty_table \<Longrightarrow>
     list_all P zs \<and> list_all P xs'"
  by (induct I xs ts arbitrary: zs xs' ts' rule: mprev_next.induct)
    (auto split: prod.splits)

lemma produces_MPrev:
  assumes p: "produces n A \<phi>" and bf: "list_all (ftable n A) buf"
  shows "produces n A (mformula.MPrev I \<phi> first buf nts)"
proof (rule producesI[where X = "\<lambda>n' A' \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> b bs nt. \<Phi> = mformula.MPrev I \<chi> b bs nt \<and> produces n A \<chi> \<and>
       list_all (ftable n A) bs)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> b bs nt. mformula.MPrev I \<phi> first buf nts
      = mformula.MPrev I \<chi> b bs nt \<and> produces n A \<chi> \<and> list_all (ftable n A) bs)"
    using p bf by blast
next
  fix n' A' \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi> b bs nt. \<Phi> = mformula.MPrev I \<chi> b bs nt \<and>
      produces n A \<chi> \<and> list_all (ftable n A) bs)"
    and w: "wf_db db" and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> b bs nt where Phi: "\<Phi> = mformula.MPrev I \<chi> b bs nt"
    and pc: "produces n A \<chi>" and lb: "list_all (ftable n A) bs" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  have ta: "list_all (ftable n A) as" by (rule produces_tables[OF pc w e1])
  obtain ws bs' nt' where e2: "mprev_next I (bs @ as) (nt @ ts) = (ws, bs', nt')"
    by (cases "mprev_next I (bs @ as) (nt @ ts)") auto
  have out: "list_all (ftable n A) ws \<and> list_all (ftable n A) bs'"
    by (rule mprev_next_out[OF e2]) (use lb ta in \<open>auto simp: table_def\<close>)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> b bs nt. \<Phi>' = mformula.MPrev I \<chi> b bs nt \<and>
         produces n A \<chi> \<and> list_all (ftable n A) bs)) \<or> produces n' A' \<Phi>')"
    using X e Phi e1 e2 out lb ta produces_next[OF pc w e1]
    by (auto simp: table_def split: if_splits)
qed

lemma produces_MNext:
  assumes p: "produces n A \<phi>"
  shows "produces n A (mformula.MNext I \<phi> first nts)"
proof (rule producesI[where X = "\<lambda>n' A' \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> b nt. \<Phi> = mformula.MNext I \<chi> b nt \<and> produces n A \<chi>)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> b nt. mformula.MNext I \<phi> first nts
      = mformula.MNext I \<chi> b nt \<and> produces n A \<chi>)" using p by blast
next
  fix n' A' \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi> b nt. \<Phi> = mformula.MNext I \<chi> b nt \<and> produces n A \<chi>)"
    and w: "wf_db db" and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> b nt where Phi: "\<Phi> = mformula.MNext I \<chi> b nt" and pc: "produces n A \<chi>"
    by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  have ta: "list_all (ftable n A) as" by (rule produces_tables[OF pc w e1])
  obtain cs b' where c: "(case (as, b) of (_ # as', True) \<Rightarrow> (as', False) | a \<Rightarrow> a) = (cs, b')"
    by (cases "(case (as, b) of (_ # as', True) \<Rightarrow> (as', False) | a \<Rightarrow> a)") auto
  have tc: "list_all (ftable n A) cs"
    using ta c by (cases as; cases b) auto
  obtain ws cs' nt' where e2: "mprev_next I cs (nt @ ts) = (ws, cs', nt')"
    by (cases "mprev_next I cs (nt @ ts)") auto
  have out: "list_all (ftable n A) ws \<and> list_all (ftable n A) cs'"
    by (rule mprev_next_out[OF e2]) (use tc in \<open>auto simp: table_def\<close>)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> b nt. \<Phi>' = mformula.MNext I \<chi> b nt \<and> produces n A \<chi>)) \<or>
       produces n' A' \<Phi>')"
    using X e Phi e1 c e2 out produces_next[OF pc w e1] by auto
qed


subsection \<open>The aggregation node\<close>

lemma wf_tuple_insert_upd:
  "wf_tuple n B t \<Longrightarrow> y < n \<Longrightarrow> wf_tuple n (Set.insert y B) (t[y := Some v])"
  by (auto simp: wf_tuple_def nth_list_update)

lemma ftable_eval_agg:
  assumes t: "table (length tys + n) G rel" and fin: "finite rel"
    and y: "y < n" and sh: "\<forall>i \<in> G. length tys \<le> i"
    and g0: "g0 \<Longrightarrow> G = {}"
  shows "ftable n (Set.insert y ((\<lambda>i. i - length tys) ` G))
      (eval_agg n g0 y \<omega> tys trm rel)"
proof (cases "g0 \<and> rel = empty_table")
  case True
  then have G: "G = {}" using g0 by simp
  have "table n {y} (singleton_table n y (eval_agg_op \<omega> {}))" by simp
  moreover have "finite (singleton_table n y (eval_agg_op \<omega> {}))"
    by (simp add: singleton_table_def)
  ultimately show ?thesis using True by (simp add: eval_agg_def G)
next
  case False
  have w: "\<And>x. x \<in> rel \<Longrightarrow>
      wf_tuple n ((\<lambda>i. i - length tys) ` G) (drop (length tys) x)"
  proof -
    fix x assume x: "x \<in> rel"
    then have wx: "wf_tuple (length tys + n) G x" using t by (simp add: table_def)
    show "wf_tuple n ((\<lambda>i. i - length tys) ` G) (drop (length tys) x)"
      using wx sh by (fastforce simp: wf_tuple_def image_iff)
  qed
  show ?thesis
    unfolding eval_agg_def if_not_P[OF False]
    using fin w y by (auto simp: table_def Let_def intro!: wf_tuple_insert_upd)
qed

lemma produces_MAgg:
  assumes p: "produces (length (aggargs_tys args) + n) G \<phi>"
    and an: "aggargs_n args = n" and y: "aggargs_y args < n"
    and sh: "\<forall>i \<in> G. length (aggargs_tys args) \<le> i"
    and g0: "aggargs_g0 args \<Longrightarrow> G = {}"
  shows "produces n (Set.insert (aggargs_y args) ((\<lambda>i. i - length (aggargs_tys args)) ` G))
      (mformula.MAgg args \<phi>)"
proof -
  have step: "\<And>j ts db \<chi> ys \<chi>'.
      meval j (length (aggargs_tys args) + n) ts db \<chi> = (ys, \<chi>') \<Longrightarrow>
      meval j n ts db (mformula.MAgg args \<chi>) = (map (eval_aggargs args) ys, mformula.MAgg args \<chi>')"
    by simp
  have tab: "\<And>Y. table (length (aggargs_tys args) + n) G Y \<Longrightarrow> finite Y \<Longrightarrow>
      table n (Set.insert (aggargs_y args) ((\<lambda>i. i - length (aggargs_tys args)) ` G))
        (eval_aggargs args Y) \<and>
      finite (eval_aggargs args Y)"
    unfolding eval_aggargs_def an[symmetric]
    by (rule ftable_eval_agg[OF _ _ _ sh g0]) (use y an in auto)
  show ?thesis by (rule produces_unop[OF step tab p])
qed


subsection \<open>The multi-way conjunction\<close>

text \<open>
  The multi-way join's shape follows from the same fold that
  @{thm [source] dmulti_join_dtabc} uses: at well-formed operands it is the left-to-right fold of
  the positive tables followed by the anti-joins against the negative ones, and each step of both
  folds keeps the table over the accumulated columns and keeps it finite.
\<close>

lemma kands_pos_ftable:
  "list_all2 (\<lambda>A X. table n A X \<and> finite X) As Xs \<Longrightarrow> table n B T \<Longrightarrow> finite T \<Longrightarrow>
     table n (B \<union> \<Union>(set As)) (kands_pos T Xs) \<and> finite (kands_pos T Xs)"
proof (induct As arbitrary: Xs B T)
  case Nil
  then show ?case by simp
next
  case (Cons A As)
  from Cons.prems(1) obtain X Xs' where Xs: "Xs = X # Xs'"
    and hd: "table n A X" "finite X"
    and tl: "list_all2 (\<lambda>A X. table n A X \<and> finite X) As Xs'"
    by (cases Xs) auto
  have t: "table n (B \<union> A) (join T True X)"
    using Cons.prems(2) hd by (intro join_table[of n B T A X True]) auto
  have f: "finite (join T True X)" using Cons.prems(3) hd by (simp add: finite_join)
  show ?case using Cons.hyps[OF tl t f] by (simp add: Xs Un_assoc)
qed

lemma kands_neg_ftable:
  "list_all2 (\<lambda>A X. table n A X \<and> finite X) Bs Ys \<Longrightarrow> table n B T \<Longrightarrow> finite T \<Longrightarrow>
     (\<forall>A \<in> set Bs. A \<subseteq> B) \<Longrightarrow>
     table n B (kands_neg T Ys) \<and> finite (kands_neg T Ys)"
proof (induct Bs arbitrary: Ys T)
  case Nil
  then show ?case by simp
next
  case (Cons A Bs)
  from Cons.prems(1) obtain Y Ys' where Ys: "Ys = Y # Ys'"
    and hd: "table n A Y" "finite Y"
    and tl: "list_all2 (\<lambda>A X. table n A X \<and> finite X) Bs Ys'"
    by (cases Ys) auto
  have s: "A \<subseteq> B" using Cons.prems(4) by simp
  have t: "table n B (join T False Y)"
    using Cons.prems(2) hd s by (intro join_table[of n B T A Y False B]) auto
  have f: "finite (join T False Y)" using Cons.prems(3) hd by (simp add: finite_join)
  show ?case using Cons.hyps[OF tl t f] Cons.prems(4) by (simp add: Ys)
qed

lemma ftable_mmulti_join:
  assumes lp: "length As = length Xs" and ln: "length A_neg = length L_neg"
    and lpos: "list_all2 (\<lambda>A X. table n A X \<and> finite X \<and> wf_set n A) As Xs"
    and lneg: "list_all2 (\<lambda>A X. table n A X \<and> finite X \<and> wf_set n A) A_neg L_neg"
    and t0: "table n A0 X0" and f0: "finite X0" and w0: "wf_set n A0"
    and sub: "\<forall>B \<in> set A_neg. B \<subseteq> A0 \<union> \<Union>(set As)"
  shows "ftable n (A0 \<union> \<Union>(set As)) (mmulti_join n (A0 # As) A_neg ((X0 # Xs) @ L_neg))"
proof -
  let ?A = "A0 \<union> \<Union>(set As)"
  let ?K = "kands_pos X0 Xs"
  have lpos': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) As Xs"
    by (rule list_all2_mono[OF lpos]) auto
  have lneg': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_neg L_neg"
    by (rule list_all2_mono[OF lneg]) auto
  have lposf: "list_all2 (\<lambda>A X. table n A X \<and> finite X) As Xs"
    by (rule list_all2_mono[OF lpos]) auto
  have lnegf: "list_all2 (\<lambda>A X. table n A X \<and> finite X) A_neg L_neg"
    by (rule list_all2_mono[OF lneg]) auto
  have la': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
      ((A0 # As) @ A_neg) ((X0 # Xs) @ L_neg)"
    using t0 w0 lpos' lneg' by (simp add: list_all2_appendI)
  have subU: "\<Union>(set A_neg) \<subseteq> \<Union>(set (A0 # As))" using sub by auto
  have tk: "table n ?A ?K" and fk: "finite ?K"
    using kands_pos_ftable[OF lposf t0 f0] by auto
  have wA: "wf_set n ?A"
  proof -
    have "\<And>i. i < length As \<Longrightarrow> wf_set n (As ! i)"
      using lpos by (auto dest: list_all2_nthD)
    then have "\<And>C. C \<in> set As \<Longrightarrow> wf_set n C" by (auto simp: in_set_conv_nth)
    then show ?thesis using w0 by (auto simp: wf_set_def)
  qed
  have eq1: "mmulti_join n (A0 # As) A_neg ((X0 # Xs) @ L_neg)
      = mmulti_join' (A0 # As) A_neg ((X0 # Xs) @ L_neg)"
    by (rule mmulti_join_eq_mmulti_join'[OF _ la' subU]) simp
  have eq2: "mmulti_join' (A0 # As) A_neg ((X0 # Xs) @ L_neg)
      = mmulti_join' [?A] A_neg (?K # L_neg)"
    by (rule mmulti_join'_fold_pos[OF lp la'])
  have eq3: "mmulti_join' [?A] A_neg (?K # L_neg) = kands_neg ?K L_neg"
  proof (rule mmulti_join'_fold_neg[OF ln])
    show "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) ([?A] @ A_neg) ([?K] @ L_neg)"
      using tk wA lneg' by (simp add: list_all2_appendI)
    show "\<forall>B \<in> set A_neg. B \<subseteq> ?A" by (rule sub)
  qed
  show ?thesis unfolding eq1 eq2 eq3
    using kands_neg_ftable[OF lnegf tk fk sub] by simp
qed

lemma mbufn_take_out:
  "mbufn_take f z buf = (w, buf') \<Longrightarrow> length Ss = length buf \<Longrightarrow>
   (\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i) \<Longrightarrow>
   (\<And>as u. length as = length Ss \<Longrightarrow> (\<forall>i < length Ss. as ! i \<in> Ss ! i) \<Longrightarrow> Q u \<Longrightarrow>
      Q (f as u)) \<Longrightarrow>
   Q z \<Longrightarrow>
   Q w \<and> length buf' = length buf \<and> (\<forall>i < length buf'. set (buf' ! i) \<subseteq> Ss ! i)"
proof (induct f z buf arbitrary: w buf' rule: mbufn_take.induct)
  case (1 f z buf)
  note IH = 1(1) and E = 1(2) and L = 1(3) and SUB = 1(4) and ST = 1(5) and QZ = 1(6)
  show ?case
  proof (cases "buf = [] \<or> [] \<in> set buf")
    case True
    then show ?thesis using E L SUB QZ by simp
  next
    case False
    then have ne: "\<And>i. i < length buf \<Longrightarrow> buf ! i \<noteq> []" by (auto simp: in_set_conv_nth)
    have las: "length (map hd buf) = length Ss" using L by simp
    have has: "\<forall>i < length Ss. map hd buf ! i \<in> Ss ! i"
    proof (intro allI impI)
      fix i assume i: "i < length Ss"
      then have ib: "i < length buf" using L by simp
      have "hd (buf ! i) \<in> set (buf ! i)" using ne[OF ib] by simp
      then show "map hd buf ! i \<in> Ss ! i" using SUB ib by auto
    qed
    have q: "Q (f (map hd buf) z)" by (rule ST[OF las has QZ])
    have lt: "length Ss = length (map tl buf)" using L by simp
    have st: "\<forall>i < length (map tl buf). set (map tl buf ! i) \<subseteq> Ss ! i"
      using SUB L by (auto dest: set_tl_sub[THEN subsetD])
    have e: "mbufn_take f (f (map hd buf) z) (map tl buf) = (w, buf')"
      using E False by simp
    show ?thesis using IH[OF False e lt st ST q] L by simp
  qed
qed

lemma ftable_mmulti_join':
  assumes lall: "list_all2 (\<lambda>C X. table n C X \<and> finite X \<and> wf_set n C)
      ((A0 # As) @ A_neg) L"
    and sub: "\<forall>B \<in> set A_neg. B \<subseteq> A0 \<union> \<Union>(set As)"
  shows "ftable n (A0 \<union> \<Union>(set As)) (mmulti_join n (A0 # As) A_neg L)"
proof -
  let ?Q = "\<lambda>C X. table n C X \<and> finite X \<and> wf_set n C"
  obtain X0 R where L0: "L = X0 # R" and h0: "?Q A0 X0"
    and rest: "list_all2 ?Q (As @ A_neg) R"
    using lall by (auto simp: list_all2_Cons1)
  obtain Xs N where R: "R = Xs @ N" and lXs: "length Xs = length As"
    and lpos: "list_all2 ?Q As Xs" and sn: "list_all2 ?Q A_neg N"
    using rest by (auto simp: list_all2_append1)
  have lN: "length A_neg = length N" by (rule list_all2_lengthD[OF sn])
  have t0: "table n A0 X0" and f0: "finite X0" and w0: "wf_set n A0"
    using h0 by simp_all
  have L: "L = (X0 # Xs) @ N" by (simp add: L0 R)
  show ?thesis unfolding L
    by (rule ftable_mmulti_join[OF lXs[symmetric] lN lpos sn t0 f0 w0 sub])
qed


lemma ftable_mmulti_join_nth:
  fixes as :: "event_data table list"
  assumes la: "length as = length ((A0 # As) @ A_neg)"
    and ha: "\<forall>i < length as. ftable n (((A0 # As) @ A_neg) ! i) (as ! i)"
    and wf: "\<forall>C \<in> set ((A0 # As) @ A_neg). wf_set n C"
    and sub: "\<forall>B \<in> set A_neg. B \<subseteq> A0 \<union> \<Union>(set As)"
  shows "ftable n (A0 \<union> \<Union>(set As)) (mmulti_join n (A0 # As) A_neg as)"
proof -
  have wfi: "\<And>i. i < length ((A0 # As) @ A_neg) \<Longrightarrow> wf_set n (((A0 # As) @ A_neg) ! i)"
    using wf by (meson nth_mem)
  show ?thesis
    by (rule ftable_mmulti_join'[OF _ sub])
      (use la ha wfi in \<open>auto simp: list_all2_conv_all_nth\<close>)
qed

lemma produces_MAnds:
  assumes lL: "length L = length ((A0 # As) @ A_neg)"
    and lb: "length buf = length ((A0 # As) @ A_neg)"
    and pL: "\<forall>i < length ((A0 # As) @ A_neg). produces n (((A0 # As) @ A_neg) ! i) (L ! i)"
    and pb: "\<forall>i < length ((A0 # As) @ A_neg).
        list_all (ftable n (((A0 # As) @ A_neg) ! i)) (buf ! i)"
    and wf: "\<forall>C \<in> set ((A0 # As) @ A_neg). wf_set n C"
    and sub: "\<forall>B \<in> set A_neg. B \<subseteq> A0 \<union> \<Union>(set As)"
    and A: "A = A0 \<union> \<Union>(set As)"
  shows "produces n A (mformula.MAnds (A0 # As) A_neg L buf)"
proof (rule producesI[where X = "\<lambda>n' A' \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>M bf. \<Phi> = mformula.MAnds (A0 # As) A_neg M bf \<and>
       length M = length ((A0 # As) @ A_neg) \<and>
       length bf = length ((A0 # As) @ A_neg) \<and>
       (\<forall>i < length ((A0 # As) @ A_neg).
          produces n (((A0 # As) @ A_neg) ! i) (M ! i)) \<and>
       (\<forall>i < length ((A0 # As) @ A_neg).
          list_all (ftable n (((A0 # As) @ A_neg) ! i)) (bf ! i)))"])
  show "n = n \<and> A = A \<and> (\<exists>M bf. mformula.MAnds (A0 # As) A_neg L buf
      = mformula.MAnds (A0 # As) A_neg M bf \<and>
      length M = length ((A0 # As) @ A_neg) \<and> length bf = length ((A0 # As) @ A_neg) \<and>
      (\<forall>i < length ((A0 # As) @ A_neg). produces n (((A0 # As) @ A_neg) ! i) (M ! i)) \<and>
      (\<forall>i < length ((A0 # As) @ A_neg).
         list_all (ftable n (((A0 # As) @ A_neg) ! i)) (bf ! i)))"
    using lL lb pL pb by blast
next
  fix n' A' \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>M bf. \<Phi> = mformula.MAnds (A0 # As) A_neg M bf \<and>
      length M = length ((A0 # As) @ A_neg) \<and> length bf = length ((A0 # As) @ A_neg) \<and>
      (\<forall>i < length ((A0 # As) @ A_neg). produces n (((A0 # As) @ A_neg) ! i) (M ! i)) \<and>
      (\<forall>i < length ((A0 # As) @ A_neg).
         list_all (ftable n (((A0 # As) @ A_neg) ! i)) (bf ! i)))"
    and w: "wf_db db" and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  define Cs where "Cs = (A0 # As) @ A_neg"
  from X obtain M0 bf0 where Phi: "\<Phi> = mformula.MAnds (A0 # As) A_neg M0 bf0"
    and lM: "length M0 = length Cs" and lbf: "length bf0 = length Cs"
    and pM: "\<forall>i < length Cs. produces n (Cs ! i) (M0 ! i)"
    and pbf: "\<forall>i < length Cs. list_all (ftable n (Cs ! i)) (bf0 ! i)"
    unfolding Cs_def by blast
  define R where "R = map (meval j n ts db) M0"
  define bf1 where "bf1 = mbufn_add (map fst R) bf0"
  define Ss :: "event_data table set list" where "Ss = map (\<lambda>C. {X. ftable n C X}) Cs"
  define f :: "event_data table list \<Rightarrow> event_data table list \<Rightarrow> event_data table list"
    where "f = (\<lambda>as zs. zs @ [mmulti_join n (A0 # As) A_neg as])"
  have lR: "length R = length Cs" using lM by (simp add: R_def)
  have lb1: "length bf1 = length Cs" using lbf lR by (simp add: bf1_def)
  have lSs: "length Ss = length Cs" by (simp add: Ss_def)
  have tR: "\<And>i. i < length Cs \<Longrightarrow> list_all (ftable n (Cs ! i)) (fst (R ! i))"
  proof -
    fix i assume i: "i < length Cs"
    obtain as \<chi>' where ei: "meval j n ts db (M0 ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M0 ! i)")
    have "list_all (ftable n (Cs ! i)) as"
      by (rule produces_tables[OF _ w ei]) (use pM i in blast)
    then show "list_all (ftable n (Cs ! i)) (fst (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have nR: "\<And>i. i < length Cs \<Longrightarrow> produces n (Cs ! i) (snd (R ! i))"
  proof -
    fix i assume i: "i < length Cs"
    obtain as \<chi>' where ei: "meval j n ts db (M0 ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M0 ! i)")
    have "produces n (Cs ! i) \<chi>'"
      by (rule produces_next[OF _ w ei]) (use pM i in blast)
    then show "produces n (Cs ! i) (snd (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have sub1: "\<forall>i < length bf1. set (bf1 ! i) \<subseteq> Ss ! i"
  proof (intro allI impI)
    fix i assume i: "i < length bf1"
    then have ic: "i < length Cs" using lb1 by simp
    have "bf1 ! i = bf0 ! i @ fst (R ! i)" using ic lbf lR by (simp add: bf1_def)
    then show "set (bf1 ! i) \<subseteq> Ss ! i"
      using pbf tR[OF ic] ic by (auto simp: Ss_def list_all_iff)
  qed
  have st: "\<And>as u. length as = length Ss \<Longrightarrow> (\<forall>i < length Ss. as ! i \<in> Ss ! i) \<Longrightarrow>
      list_all (ftable n A) u \<Longrightarrow> list_all (ftable n A) (f as u)"
  proof -
    fix as :: "event_data table list" and u :: "event_data table list"
    assume la: "length as = length Ss" and ha: "\<forall>i < length Ss. as ! i \<in> Ss ! i"
      and qu: "list_all (ftable n A) u"
    have ha': "\<forall>i < length Cs. ftable n (Cs ! i) (as ! i)"
    proof (intro allI impI)
      fix i assume i: "i < length Cs"
      then have "as ! i \<in> Ss ! i" using ha lSs by simp
      then show "ftable n (Cs ! i) (as ! i)" using i by (simp add: Ss_def)
    qed
    have lac: "length as = length ((A0 # As) @ A_neg)" using la lSs by (simp add: Cs_def)
    have hac: "\<forall>i < length as. ftable n (((A0 # As) @ A_neg) ! i) (as ! i)"
      using ha' la lSs by (simp add: Cs_def)
    have "ftable n A (mmulti_join n (A0 # As) A_neg as)"
      unfolding A by (rule ftable_mmulti_join_nth[OF lac hac wf sub])
    then show "list_all (ftable n A) (f as u)" using qu by (simp add: f_def)
  qed
  obtain zs bf2 where e2: "mbufn_take f [] bf1 = (zs, bf2)"
    by (cases "mbufn_take f [] bf1")
  have lSb: "length Ss = length bf1" using lSs lb1 by simp
  have qz: "list_all (ftable n A) []" by simp
  have out: "list_all (ftable n A) zs \<and> length bf2 = length bf1 \<and>
      (\<forall>i < length bf2. set (bf2 ! i) \<subseteq> Ss ! i)"
    by (rule mbufn_take_out[where Q = "list_all (ftable n A)" and f = f and Ss = Ss,
        OF e2 lSb sub1 st qz])
  have m: "meval j n ts db (mformula.MAnds (A0 # As) A_neg M0 bf0)
      = (zs, mformula.MAnds (A0 # As) A_neg (map snd R) bf2)"
    using e2 unfolding R_def bf1_def f_def
    by (simp add: Let_def del: mbufn_take.simps mmulti_join.simps)
  have x: "xs = zs" and f': "\<Phi>' = mformula.MAnds (A0 # As) A_neg (map snd R) bf2"
    using e X Phi m by simp_all
  have pM': "\<forall>i < length Cs. produces n (Cs ! i) (map snd R ! i)"
    using nR lR by simp
  have pbf': "\<forall>i < length Cs. list_all (ftable n (Cs ! i)) (bf2 ! i)"
    using out lb1 by (auto simp: Ss_def list_all_iff subset_eq)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>M bf. \<Phi>' = mformula.MAnds (A0 # As) A_neg M bf \<and>
         length M = length ((A0 # As) @ A_neg) \<and>
         length bf = length ((A0 # As) @ A_neg) \<and>
         (\<forall>i < length ((A0 # As) @ A_neg). produces n (((A0 # As) @ A_neg) ! i) (M ! i)) \<and>
         (\<forall>i < length ((A0 # As) @ A_neg).
            list_all (ftable n (((A0 # As) @ A_neg) ! i)) (bf ! i)))) \<or>
       produces n' A' \<Phi>')"
    using X out pM' pbf' lM lb1 lR by (auto simp: x f' Cs_def)
qed

(*<*)
end
(*>*)
